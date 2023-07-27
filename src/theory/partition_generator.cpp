/******************************************************************************
 * Top contributors (to current version):
 *   Amalee Wilson, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * PartitionGenerator for creating partitions.
 */

#include "theory/partition_generator.h"

#include <math.h>
#include <random>
#include <algorithm>

#include "expr/node_algorithm.h"
#include "expr/node_builder.h"
#include "options/parallel_options.h"
#include "prop/prop_engine.h"
#include "prop/theory_proxy.h"
#include "prop/zero_level_learner.h"
#include "theory/rewriter.h"
#include "theory/theory_engine.h"
#include "theory/theory_id.h"
#include "theory/theory_traits.h"

using namespace std;

namespace cvc5::internal {

namespace theory {
PartitionGenerator::PartitionGenerator(Env& env,
                                       TheoryEngine* theoryEngine,
                                       prop::PropEngine* propEngine)
    : TheoryEngineModule(env, theoryEngine, "PartitionGenerator"),
      d_numPartitions(options().parallel.computePartitions),
      d_numChecks(0),
      d_betweenChecks(0),
      d_numPartitionsSoFar(0),
      d_createdAnyPartitions(false),
      d_emittedAllPartitions(false)
{
  d_startTime = std::chrono::steady_clock::now();
  d_startTimeOfPreviousPartition = std::chrono::steady_clock::now();
  d_valuation = std::make_unique<Valuation>(theoryEngine);
  d_propEngine = propEngine;

  d_conflictSize = options().parallel.partitionConflictSize;
  if (!d_conflictSize)
  {
    d_conflictSize = static_cast<uint64_t>(log2(d_numPartitions));
  }
}

void PartitionGenerator::addLemmaLiteral(Node toAdd)
{
  if (options().parallel.partitionStrategy
          == options::PartitionMode::LEMMA_CUBES
      || options().parallel.partitionStrategy
             == options::PartitionMode::LEMMA_DNCS)
  {
    std::vector<Node> toVisit;
    toVisit.push_back(toAdd);

    for (unsigned i = 0; i < toVisit.size(); ++i)
    {
      Node current = toVisit[i];
      // If current node is theory bool, visit the children.
      if (Theory::theoryOf(current) == THEORY_BOOL)
      {
        for (unsigned child = 0, childEnd = current.getNumChildren();
             child < childEnd;
             ++child)
        {
          auto childNode = current[child];
          // If we haven't seens the child, we should visit it.
          if (d_lemmaMap.count(childNode) == 0)
          {
            toVisit.push_back(childNode);
          }
          else
          {
            // If we have already seen this chld node, then it is not theory
            // bool, so we update its entry. No need to visit again.
            int new_count = d_lemmaMap[childNode] + 1; 
            d_lemmaMap.erase(childNode);
            d_lemmaMap.insert({childNode, new_count});
          }
        }
      }
      else
      {
        if (d_lemmaMap.count(current) == 0)
        {
          d_lemmaMap.insert({current, 1});
          d_lemmaLiterals.insert(current);
        }
        else
        {
          int new_count = d_lemmaMap[current] + 1;
          d_lemmaMap.erase(current);
          d_lemmaMap.insert({current, new_count});
        }
      }
    }
  }
}

// Some of this function may actually be redundant, but I was trying to be
// complete.
bool PartitionGenerator::isUnusable(Node n)
{
  const std::unordered_set<Kind, kind::KindHashFunction> skolemKinds = {
      kind::SKOLEM};
  const std::unordered_set<Kind, kind::KindHashFunction> unusableKinds = {
      kind::INST_CONSTANT};

  // Check if n is constant or contains unusable kinds.
  if (n.isConst() || expr::hasSubtermKinds(unusableKinds, n))
  {
    return true;
  }

  // Check if original has unusable kinds.
  Node originalN = SkolemManager::getOriginalForm(n);
  if (expr::hasSubtermKinds(unusableKinds, originalN))
  {
    return true;
  }

  // Get non negated versions before testing for bool expr.
  Node nonNegatedN = n.getKind() == kind::NOT ? n[0] : n;
  Node nonNegatedOriginal =
      originalN.getKind() == kind::NOT ? originalN[0] : originalN;

  // Check if this is a boolean expression
  if (Theory::theoryOf(nonNegatedN) == THEORY_BOOL
      || Theory::theoryOf(nonNegatedOriginal) == THEORY_BOOL)
  {
    return true;
  }

  // If the original form has skolems, then we cannot use it.
  if (expr::hasSubtermKinds(skolemKinds, n)
      && expr::hasSubtermKinds(skolemKinds, originalN))
  {
    return true;
  }

  return false;
}

void PartitionGenerator::usePriorityHeuristic(
    std::vector<Node>& unfilteredLiterals, std::vector<Node>& filteredLiterals)
{
  const std::unordered_set<Kind, kind::KindHashFunction> skolemKinds = {
      kind::SKOLEM};
  // We select literals / theory atoms with the following priority:
  // 1. The atom has no skolems and appears in the input.
  // 2. The original form has no skolems and appears in the input.
  // 3. The atom has no skolems and does not appear in the input.
  // 4. The original form has no skolems and does not appear in the input.
  // NOTE: we should probably experiment with these priorities.
  //       maybe do all permutations on a small subset of problems?
  //       seems annoying... but maybe I can make it an option.
  //       portfolio paritioning?

  std::vector<Node> inputNoSkolems;
  std::vector<Node> inputWithSkolems;
  std::vector<Node> notInputNoSkolems;
  std::vector<Node> notInputWithSkolems;

  for (const Node& n : unfilteredLiterals)
  {
    if (isUnusable(n))
    {
      continue;
    }

    Node originalN = SkolemManager::getOriginalForm(n);

    // A segfault is getting produced when we try to get the learned lit type
    // for the nodes with skolems (not all of them, but some of them.)
    modes::LearnedLitType nType = d_propEngine->getLiteralType(n);
    modes::LearnedLitType originalNType = d_propEngine->getLiteralType(originalN);

    // inputNoSkolems
    if (!expr::hasSubtermKinds(skolemKinds, n)
        && nType == modes::LEARNED_LIT_INPUT)
    {
      inputNoSkolems.push_back(n);
    }
    // inputWithSkolems
    else if (!expr::hasSubtermKinds(skolemKinds, originalN)
             && originalNType == modes::LEARNED_LIT_INPUT)
    {
      inputWithSkolems.push_back(originalN);
    }
    // notInputNoSkolems
    else if (!expr::hasSubtermKinds(skolemKinds, n))
    {
      notInputNoSkolems.push_back(n);
    }
    // notInputWithSkolems
    else if (!expr::hasSubtermKinds(skolemKinds, originalN))
    {
      notInputWithSkolems.push_back(originalN);
    }
    else
    {
      continue;
    }
  }

  // Here we sort the potential literals/atoms for splitting. 
  // TODO: Experiment with this ordering?
  for (auto candidateNode : inputNoSkolems)
  {
    filteredLiterals.push_back(candidateNode);
  }
  for (auto candidateNode : inputWithSkolems)
  {
    filteredLiterals.push_back(candidateNode);
  }
  for (auto candidateNode : notInputNoSkolems)
  {
    filteredLiterals.push_back(candidateNode);
  }
  for (auto candidateNode : notInputWithSkolems)
  {
    filteredLiterals.push_back(candidateNode);
  }
}

std::vector<Node> PartitionGenerator::collectLiterals(LiteralListType litType)
{
  std::vector<Node> filteredLiterals;
  std::vector<Node> unfilteredLiterals;

  // These kinds are used to filter out the types of literals we don't want.
  const std::unordered_set<Kind, kind::KindHashFunction> kinds = {
      kind::SKOLEM};
  const std::unordered_set<Kind, kind::KindHashFunction> unusableKinds = {
      kind::INST_CONSTANT};

  switch (litType)
  {
    case DECISION:
    {
      unfilteredLiterals = d_propEngine->getPropDecisions();
      break;
    }
    case HEAP:
    {
      unfilteredLiterals = d_propEngine->getPropOrderHeap();
      break;
    }
    case LEMMA:
    {
      std::vector<Node> lemmaNodes(d_lemmaLiterals.size());
      std::copy(
          d_lemmaLiterals.begin(), d_lemmaLiterals.end(), lemmaNodes.begin());
      unfilteredLiterals = lemmaNodes;
      break;
    }
    case ZLL:
    {
      unfilteredLiterals =
          d_propEngine->getLearnedZeroLevelLiterals(modes::LEARNED_LIT_INPUT);
      break;
    }
    default: return filteredLiterals;
  }

  if (litType == HEAP || litType == DECISION)
  {
    if (options().parallel.prioritizeLiterals)
    {
      usePriorityHeuristic(unfilteredLiterals, filteredLiterals);
    }
    else
    {
      for (const Node& n : unfilteredLiterals)
      {
        Node originalN = SkolemManager::getOriginalForm(n);
        if (isUnusable(n))
        {
          continue;
        }
        filteredLiterals.push_back(originalN);
      }
    }
  }
  else if (litType == LEMMA)
  {
    // Sort by frequency of the literal.
    std::sort(unfilteredLiterals.begin(),
              unfilteredLiterals.end(),
              [this](Node a, Node b) -> bool {
                return d_lemmaMap[a] > d_lemmaMap[b];
              });

    if (options().parallel.prioritizeLiterals)
    {
      // Need to use rewriter to avoid segfault issue here.
      Rewriter rewriter;
      std::vector<Node> rewritten;
      for (auto l : unfilteredLiterals)
      {
        rewritten.push_back(rewriter.rewrite(l));
      }
      usePriorityHeuristic(rewritten, filteredLiterals);
    }
    else
    {
      for (auto lit : unfilteredLiterals)
      {
        if (isUnusable(lit))
        {
          continue;
        }
        // Skip lemma literals that we have used.
        if (d_usedLemmaLiterals.count(lit) != 0)
        {
          continue;
        }
        filteredLiterals.push_back(SkolemManager::getOriginalForm(lit));
      }
    }
  }
  // else it must be zll
  else
  {
    // I'm pretty sure that these checks are unnecessary for ZLL.
    for (const Node& n : unfilteredLiterals)
    {
      Node originalN = SkolemManager::getOriginalForm(n);
      if (isUnusable(n))
      {
        continue;
      }
      filteredLiterals.push_back(originalN);
    }
  }
  return filteredLiterals;
}

// Here we want to make sure that the proper number of partitions are emitted.
void PartitionGenerator::emitPendingPartitions(bool solved)
{
  if (!d_emittedAllPartitions)
  {
    bool emitZLL = options().parallel.appendLearnedLiteralsToCubes;
    if (options().parallel.useBackupCubes)
    {
      // If we have not emitted all partitions, then we need to
      // decide what partitions we will emit. The most straightforward
      // backup strategy is to cube on the available partitions.
      // Now this can be done in two ways: either we have enough DNCs
      // to cube on the DNCs themselves, or we don't, and we will cube on the
      // literals available in the first DNC. Note a major assumption here:
      // We are assuming that the number of literals in the first DNC is at
      // least log2 of the requested number of partitions, which is the default.
      // We will need to update this code to be more robust in the event that
      // the number of literals in the first DNC is less than log2 of the
      // requested number of partitions.

      std::vector<Node> literals;

      if (d_cubes.size() < d_conflictSize)
      {
        // Then we must cube on the literals in the first cube.
        size_t numChildren = d_cubes[0].getNumChildren();
        for (size_t i = 0; i < numChildren; ++i)
        {
          literals.push_back(d_cubes[0][i]);
        }
      }
      else
      {
        // Then we can cube on the cubes themselves.
        for (size_t i = 0; i < d_conflictSize; ++i)
        {
          literals.push_back(d_cubes[i]);
        }
      }

      uint64_t numVar = static_cast<uint64_t>(log2(d_numPartitions));
      if (literals.size() >= numVar)
      {
        // total number of cubes/rows
        size_t total = pow(2, numVar);

        // resultNodeLists is built column by column.
        std::vector<std::vector<Node> > resultNodeLists(total);

        // t is used to determine whether to push the node or its not_node.
        bool t = false;

        size_t numConsecutiveTF = total / 2;
        for (Node n : literals)
        {
          Node notN;
          if (n.getKind() != kind::NOT)
          {
            notN = n.notNode();
          }
          else if (n.getKind() == kind::NOT)
          {
            notN = n[0];
          }

          // loc tracks which row/cube we're on
          size_t loc = 0;
          for (size_t z = 0; z < total / numConsecutiveTF; ++z)
          {
            t = !t;
            for (size_t j = 0; j < numConsecutiveTF; ++j)
            {
              resultNodeLists[loc].push_back(t ? n : notN);
              ++loc;
            }
          }

          numConsecutiveTF = numConsecutiveTF / 2;
        }
        for (const std::vector<Node>& row : resultNodeLists)
        {
          Node conj = NodeManager::currentNM()->mkAnd(row);
          if (emitZLL)
          {
            std::vector<Node> zllLiterals = collectLiterals(ZLL);
            zllLiterals.push_back(conj);
            Node zllConj = NodeManager::currentNM()->mkAnd(zllLiterals);
            emitPartition(zllConj);
          }
          else
          {
            emitPartition(conj);
          }
        }
      }
      else
      {
        std::cout
            << "error: not enough children in first cube for backup strategy"
            << std::endl;
      }
    }
    // If not using backup cubing, then we just emit the partitions that we
    // have. If we have solved the partition, then we emit the partitions
    // available, but if not, then we must emit the final partition as well.
    else
    {
      if (solved)
      {
        // If solved, then we can just emit the partitions in d_dncs because
        // the final partition has already been solved by our current instance.
        if (emitZLL)
        {
          std::vector<Node> zllLiterals =
              d_propEngine->getLearnedZeroLevelLiterals(
                  modes::LEARNED_LIT_INPUT);

          // Add the ZLL literals to each of the partitions
          for (const auto& partition : d_dncs)
          {
            zllLiterals.push_back(partition);
            Node lemma = NodeManager::currentNM()->mkAnd(zllLiterals);
            emitPartition(lemma);
            zllLiterals.pop_back();
          }
        }
        else
        {
          for (const auto& partition : d_dncs)
          {
            emitPartition(partition);
          }
        }
      }
      else
      {
        // First, emit the first n-1 partitions.
        if (emitZLL)
        {
          std::vector<Node> zllLiterals =
              d_propEngine->getLearnedZeroLevelLiterals(
                  modes::LEARNED_LIT_INPUT);

          // Add the ZLL literals to each of the partitions
          for (const auto& partition : d_dncs)
          {
            zllLiterals.push_back(partition);
            Node lemma = NodeManager::currentNM()->mkAnd(zllLiterals);
            emitPartition(lemma);
            zllLiterals.pop_back();
          }
        }
        else
        {
          for (const auto& partition : d_dncs)
          {
            emitPartition(partition);
          }
        }

        // Now emit the final partition.
        vector<Node> nots;
        for (const Node& cube : d_cubes)
        {
          nots.push_back(cube.notNode());
        }

        Node finalPartition = NodeManager::currentNM()->mkAnd(nots);
        // Emit not(cube_one) and not(cube_two) and ... and not(cube_n-1)
        if (emitZLL)
        {
          std::vector<Node> zllLiterals =
              d_propEngine->getLearnedZeroLevelLiterals(
                  modes::LEARNED_LIT_INPUT);
          zllLiterals.push_back(finalPartition);
          Node zllFinalPartition = NodeManager::currentNM()->mkAnd(zllLiterals);
          emitPartition(zllFinalPartition);
        }
        else
        {
          emitPartition(finalPartition);
        }
      }
    }
  }
}

void PartitionGenerator::emitPartition(Node toEmit)
{
  *options().parallel.partitionsOut << toEmit << std::endl;
  ++d_numPartitionsSoFar;
  d_createdAnyPartitions = true;
}

Node PartitionGenerator::blockPath(TNode toBlock)
{
  // Now block the path in the search.
  Node lemma = toBlock.notNode();
  d_assertedLemmas.push_back(lemma);
  return lemma;
}

// Send lemma that is the negation of all previously asserted lemmas.
Node PartitionGenerator::stopPartitioning()
{
  d_emittedAllPartitions = true;
  return NodeManager::currentNM()->mkConst(false);
}

// For the DNC strategy, we make the following kinds of partitions:
// P1 =              C1 = l1_{1} & ... & l1_{d_conflictSize}
// P2 = !C1 &        C2 = l2_{1} & ... & l2_{d_conflictSize}
// P3 = !C1 & !C2 &  C3 = l3_{1} & ... & l3_{d_conflictSize}
// P4 = !C1 & !C2 & !C3
// Note that we want to simply collect the partitions until we get to the
// timeout or total number of requested partitions.
// Once we reach that point, we dump all the partitions.
Node PartitionGenerator::makeDisjointNonCubePartitions(
    LiteralListType litType, bool emitZLL, bool timedOut, bool useTrailTail, bool randomize)
{
  size_t conflictSize = d_conflictSize;
  if (options().parallel.progressiveDNCs)
  {
    size_t numPartitionsMade = d_cubes.size();
    size_t maxConflictSize = options().parallel.maxConflictSize;
    size_t minConflictSize = options().parallel.minConflictSize;
    size_t conflictSizeInterval = options().parallel.conflictSizeInterval;

    if ((numPartitionsMade * conflictSizeInterval) >= maxConflictSize)
    {
      conflictSize = minConflictSize;
    }
    else
    {
      conflictSize =
          maxConflictSize - (numPartitionsMade * conflictSizeInterval);
    }
  }

  // If we're not at the last cube
  if (d_numPartitionsSoFar < d_numPartitions - 1)
  {
    std::vector<Node> literals = collectLiterals(litType);

    // Make sure we have enough literals.
    // Conflict size can be set through options, but the default is log base 2
    // of the requested number of partitions.
    if (literals.size() < conflictSize)
    {
      if (options().parallel.takeWhatYouCan)
      {
        if (literals.size() < options().parallel.minConflictSize)
        {
          return Node::null();
        }
        // else continue
      }
      else
      {
        return Node::null();
      }
    }
    else
    {
      if (useTrailTail)
      {
        std::vector<Node> tailLits(literals.end() - conflictSize,
                                   literals.end());
        literals = tailLits;
      }
      else if (randomize)
      {
        std::shuffle(literals.begin(), literals.end(), std::mt19937(std::random_device()()));
        literals.resize(conflictSize);
      }
      else
      {
        literals.resize(conflictSize);
      }
    }

    // Add literals to the seen list if we are using lemmas
    if (options().parallel.partitionStrategy
        == options::PartitionMode::LEMMA_DNCS)
    {
      for (auto l : literals)
      {
        d_usedLemmaLiterals.insert(l);
      }
    }
    // If clearing all lemmas between partitions, do so
    if (options().parallel.clearAllLemmas)
    {
      d_lemmaMap.clear();
      d_lemmaLiterals.clear();
    }

    // Make a cube from the literals
    Node conj = NodeManager::currentNM()->mkAnd(literals);

    // For the strict-cube strategy, cubes look like the following:
    // P1 =              C1 = l1_{1} & .... & l1_{d_conflictSize}
    // P2 = !C1 &        C2 = l2_{1} & .... & l2_{d_conflictSize}
    // P3 = !C1 & !C2 &  C3 = l3_{1} & .... & l3_{d_conflictSize}
    // P4 = !C1 & !C2 & !C3
    vector<Node> toEmit;
    // Collect negation of the previously used cubes.
    for (const Node& c : d_cubes)
    {
      toEmit.push_back(c.notNode());
    }
    toEmit.push_back(conj);
    Node dnc = NodeManager::currentNM()->mkAnd(toEmit);
    d_dncs.push_back(dnc);

    // just increment and don't actually output the partition yet
    d_numPartitionsSoFar++;

    // Add the conjunction to the list of cubes.
    d_cubes.push_back(conj);

    // Track that we have created at least one partition
    d_createdAnyPartitions = true;

    if (timedOut)
    {
      emitPendingPartitions(/*solved=*/false);
      return stopPartitioning();
    }

    return blockPath(conj);
  }
  // At the last cube
  else
  {
    // First, emit the first n-1 partitions.
    if (emitZLL)
    {
      std::vector<Node> zllLiterals =
          d_propEngine->getLearnedZeroLevelLiterals(modes::LEARNED_LIT_INPUT);

      // Add the ZLL literals to each of the partitions
      for (const auto& partition : d_dncs)
      {
        zllLiterals.push_back(partition);
        Node lemma = NodeManager::currentNM()->mkAnd(zllLiterals);
        emitPartition(lemma);
        zllLiterals.pop_back();
      }
    }
    else
    {
      for (const auto& partition : d_dncs)
      {
        emitPartition(partition);
      }
    }

    // Now emit the final partition.
    vector<Node> nots;
    for (const Node& cube : d_cubes)
    {
      nots.push_back(cube.notNode());
    }

    Node finalPartition = NodeManager::currentNM()->mkAnd(nots);
    // Emit not(cube_one) and not(cube_two) and ... and not(cube_n-1)
    if (emitZLL)
    {
      std::vector<Node> zllLiterals =
          d_propEngine->getLearnedZeroLevelLiterals(modes::LEARNED_LIT_INPUT);
      zllLiterals.push_back(finalPartition);
      Node zllFinalPartition = NodeManager::currentNM()->mkAnd(zllLiterals);
      emitPartition(zllFinalPartition);
    }
    else
    {
      emitPartition(finalPartition);
    }
    return stopPartitioning();
  }
}

Node PartitionGenerator::makeCubePartitions(LiteralListType litType,
                                                 bool emitZLL,
                                                 bool useTrailTail,
                                                 bool randomize)
{
  std::vector<Node> literals = collectLiterals(litType);
  uint64_t numVar = static_cast<uint64_t>(log2(d_numPartitions));
  if (literals.size() >= numVar)
  {
    if (useTrailTail)
    {
      std::vector<Node> tailLits(literals.end() - numVar, literals.end());
      literals = tailLits;
    }
    else if (randomize)
    {
      std::shuffle(literals.begin(), literals.end(), std::mt19937(std::random_device()()));
      literals.resize(numVar);
    }
    else
    {
      literals.resize(numVar);
    }
    // This complicated thing is basically making a truth table
    // of with 2^numVar variable so that each row can be emitted as a
    // partition later. Each entry in resultNodeLists is a row corresponding
    // to a cube: resultNodeLists = {
    //   { l1,  l2}
    //   { l1, !l2}
    //   {!l1,  l2}
    //   {!l1, !l2} }

    // total number of cubes/rows
    size_t total = pow(2, numVar);

    // resultNodeLists is built column by column.
    std::vector<std::vector<Node> > resultNodeLists(total);

    // t is used to determine whether to push the node or its not_node.
    bool t = false;

    // numConsecutiveTF tracks how many times the node should be consectuively
    // true or false in a column.
    // For example, if numVar=3:
    // x y z
    // T T T
    // T T F
    // T F T
    // T F F
    // F T T
    // F T F
    // F F T
    // F F F
    // For the first column, numConsecutiveTF = 4, then 2 for the second
    // column, and 1 for the third column.
    size_t numConsecutiveTF = total / 2;
    for (Node n : literals)
    {
      Node notN;
      if (n.getKind() != kind::NOT)
      {
        notN = n.notNode();
      }
      else if (n.getKind() == kind::NOT)
      {
        notN = n[0];
      }

      // loc tracks which row/cube we're on
      size_t loc = 0;
      for (size_t z = 0; z < total / numConsecutiveTF; ++z)
      {
        t = !t;
        for (size_t j = 0; j < numConsecutiveTF; ++j)
        {
          resultNodeLists[loc].push_back(t ? n : notN);
          ++loc;
        }
      }

      numConsecutiveTF = numConsecutiveTF / 2;
    }
    for (const std::vector<Node>& row : resultNodeLists)
    {
      Node conj = NodeManager::currentNM()->mkAnd(row);
      if (emitZLL)
      {
        std::vector<Node> zllLiterals = collectLiterals(ZLL);
        zllLiterals.push_back(conj);
        Node zllConj = NodeManager::currentNM()->mkAnd(zllLiterals);
        emitPartition(zllConj);
      }
      else
      {
        emitPartition(conj);
      }
    }
    return stopPartitioning();
  }
  return Node::null();
}

void PartitionGenerator::check(Theory::Effort e)
{
  if ((options().parallel.partitionCheck == options::CheckMode::FULL
       && !Theory::fullEffort(e))
      || (options().parallel.computePartitions < 2))
  {
    return;
  }

  auto now = std::chrono::steady_clock::now();
  std::chrono::duration<double> totalElapsedTime = now - d_startTime;
  std::chrono::duration<double> interElapsedTime =
      now - d_startTimeOfPreviousPartition;
  bool startTimeExceeded =
      totalElapsedTime.count() >= options().parallel.partitionStartTime;
  bool interTimeExceeded =
      interElapsedTime.count() >= options().parallel.partitionTimeInterval;
  bool timeOutExceeded =
      totalElapsedTime.count() >= options().parallel.partitionTimeLimit;

  // When using time limits, we partition if the partition start time is
  // exceeded and no partitions have been made, or when at least one partition
  // has been created and the inter-partition time limit has been exceeded
  bool timeToPartition = ((d_createdAnyPartitions && interTimeExceeded)
                          || (!d_createdAnyPartitions && startTimeExceeded));

  d_numChecks = d_numChecks + 1;
  d_betweenChecks = d_betweenChecks + 1;
  bool checkLimitExceeded =
      ((d_createdAnyPartitions
        && d_betweenChecks >= options().parallel.checksBetweenPartitions)
       || (!d_createdAnyPartitions
           && d_numChecks >= options().parallel.checksBeforePartitioning));

  switch (options().parallel.partitionWhen)
  {
    case options::PartitionWhenMode::TLIMIT:
    {
      if (!timeToPartition)
      {
        return;
      }
      // Otherwise, we partition.
      break;
    }
    case options::PartitionWhenMode::CLIMIT:
    {
      if (!checkLimitExceeded)
      {
        return;
      }
      break;
    }
    case options::PartitionWhenMode::TLIMIT_CBACKUP:
    {
      if (!checkLimitExceeded)
      {
        if (!timeToPartition)
        {
          return;
        }
      }
      break;
    }
    case options::PartitionWhenMode::CLIMIT_TBACKUP:
    {
      if (!timeToPartition)
      {
        if (!checkLimitExceeded)
        {
          return;
        }
      }
      break;
    }
  }

  // Reset betweenChecks
  d_betweenChecks = 0;

  // Reset start time of previous partition
  d_startTimeOfPreviousPartition = std::chrono::steady_clock::now();

  Node lem;
  bool emitZLL = options().parallel.appendLearnedLiteralsToCubes;
  bool useTail = options().parallel.useTail;
  bool randomize = options().parallel.randomPartitioning;
  switch (options().parallel.partitionStrategy)
  {
    case options::PartitionMode::DECISION_CUBES:
      lem = makeCubePartitions(/*litType=*/DECISION, emitZLL, useTail, randomize);
      break;
    case options::PartitionMode::HEAP_CUBES:
      lem = makeCubePartitions(/*litType=*/HEAP, emitZLL, useTail, randomize);
      break;
    case options::PartitionMode::LEMMA_CUBES:
      lem = makeCubePartitions(/*litType=*/LEMMA, emitZLL, useTail, randomize);
      break;
    case options::PartitionMode::DECISION_DNCS:
      lem = makeDisjointNonCubePartitions(
          /*litType=*/DECISION, emitZLL, timeOutExceeded, useTail, randomize);
      break;
    case options::PartitionMode::HEAP_DNCS:
      lem = makeDisjointNonCubePartitions(
          /*litType=*/HEAP, emitZLL, timeOutExceeded, useTail, randomize);
      break;
    case options::PartitionMode::LEMMA_DNCS:
      lem = makeDisjointNonCubePartitions(
          /*litType=*/LEMMA, emitZLL, timeOutExceeded, useTail, randomize);
      break;
    default: return;
  }
  // send the lemma if it exists
  if (!lem.isNull())
  {
    d_out.lemma(lem);
  }
}

}  // namespace theory
}  // namespace cvc5::internal
