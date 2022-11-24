/******************************************************************************
 * Top contributors (to current version):
 *   Amalee Wilson, Andrew Wu
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * PartitionGenerator for creating partitions.
 */

#include "theory/partition_generator.h"

#include <math.h>

#include "expr/node_algorithm.h"
#include "expr/node_builder.h"
#include "options/parallel_options.h"
#include "prop/prop_engine.h"
#include "prop/theory_proxy.h"
#include "prop/zero_level_learner.h"
#include "theory/theory_engine.h"
#include "theory/theory_id.h"
#include "theory/theory_traits.h"

using namespace std;

namespace cvc5::internal {

namespace theory {
PartitionGenerator::PartitionGenerator(Env& env,
                                       TheoryEngine* theoryEngine,
                                       prop::PropEngine* propEngine)
    : EnvObj(env),
      d_numPartitions(options().parallel.computePartitions),
      d_numChecks(0),
      d_betweenChecks(0),
      d_numPartitionsSoFar(0),
      d_emittedAnyPartitions(false)
{
  d_startTime = std::chrono::steady_clock::now();
  d_valuation = std::make_unique<Valuation>(theoryEngine);
  d_propEngine = propEngine;

  d_conflictSize = options().parallel.partitionConflictSize;
  if (!d_conflictSize)
  {
    d_conflictSize = static_cast<uint64_t>(log2(d_numPartitions));
  }
}

void PartitionGenerator::addLemmaLiteral(TrustNode toAdd)
{
  if (options().parallel.partitionStrategy
      == options::PartitionMode::LEMMA_CUBES)
  {
    Node n = toAdd.getNode();
    std::vector<Node> toVisit;
    toVisit.push_back(n);

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
            d_lemmaMap.insert_or_assign(childNode, d_lemmaMap[childNode] + 1);
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
          d_lemmaMap.insert_or_assign(current, d_lemmaMap[current] + 1);
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
      kind::SKOLEM, kind::BOOLEAN_TERM_VARIABLE};
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
      kind::SKOLEM, kind::BOOLEAN_TERM_VARIABLE};
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
    modes::LearnedLitType nType = modes::LEARNED_LIT_UNKNOWN;
    if (!expr::hasSubtermKinds(skolemKinds, n))
    {
      nType = d_propEngine->getLiteralType(n);
    }
    modes::LearnedLitType originalNType = modes::LEARNED_LIT_UNKNOWN;
    if (!expr::hasSubtermKinds(skolemKinds, originalN))
    {
      originalNType = d_propEngine->getLiteralType(originalN);
    }

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

  // Filter out the types of literals we don't want.
  // Make sure the literal does not have a boolean term or skolem in it.
  // TODO: separate filter for unusable inst_constant.
  const std::unordered_set<Kind, kind::KindHashFunction> kinds = {
      kind::SKOLEM, kind::BOOLEAN_TERM_VARIABLE};
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
      // TODO: use option to determine whether we prioritize literals based
      // on the input/skolem heuristic.
      // Additionally, make the heuristic order tweakable.
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
        Node nonNegated =
            originalN.getKind() == kind::NOT ? originalN[0] : originalN;
        if (n.isConst() || Theory::theoryOf(nonNegated) == THEORY_BOOL
            || expr::hasSubtermKinds(unusableKinds, n)
            || expr::hasSubtermKinds(unusableKinds, originalN))
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
      usePriorityHeuristic(unfilteredLiterals, filteredLiterals);
    }
    else
    {
      for (auto lit : unfilteredLiterals)
      {
        if (lit.isConst() || expr::hasSubtermKinds(unusableKinds, lit))
        {
          continue;
        }
        filteredLiterals.push_back(lit);
      }
    }
  }
  // else it must be zll
  else
  {
    for (const Node& n : unfilteredLiterals)
    {
      Node originalN = SkolemManager::getOriginalForm(n);

      // If the literal is the not of some node, do the checks for the child
      // of the not instead of the not itself.
      Node original =
          originalN.getKind() == kind::NOT ? originalN[0] : originalN;

      if (expr::hasSubtermKinds(kinds, original)
          || !d_valuation->isSatLiteral(original)
          || Theory::theoryOf(original) == THEORY_BOOL || n.isConst())
      {
        continue;
      }
      filteredLiterals.push_back(originalN);
    }
  }

  return filteredLiterals;
}

void PartitionGenerator::emitCube(Node toEmit)
{
  *options().parallel.partitionsOut << toEmit << std::endl;
  ++d_numPartitionsSoFar;
  d_emittedAnyPartitions = true;
}

TrustNode PartitionGenerator::blockPath(TNode toBlock)
{
  // Now block the path in the search.
  Node lemma = toBlock.notNode();
  d_assertedLemmas.push_back(lemma);
  TrustNode trustedLemma = TrustNode::mkTrustLemma(lemma);
  return trustedLemma;
}

// Send lemma that is the negation of all previously asserted lemmas.
TrustNode PartitionGenerator::stopPartitioning() const
{
  return TrustNode::mkTrustLemma(NodeManager::currentNM()->mkConst(false));
}

// This is the revised version of the old splitting strategy.
// Cubes look like the following:
// C1 = l1_{1} & .... & l1_{d_conflictSize}
// C2 = l2_{1} & .... & l2_{d_conflictSize}
// C3 = l3_{1} & .... & l3_{d_conflictSize}
// C4 = !C1 & !C2 & !C3
TrustNode PartitionGenerator::makeRevisedPartitions(bool strict, bool emitZLL)
{
  // If we're not at the last cube
  if (d_numPartitionsSoFar < d_numPartitions - 1)
  {
    std::vector<Node> literals = collectLiterals(DECISION);

    // Make sure we have enough literals.
    // Conflict size can be set through options, but the default is log base 2
    // of the requested number of partitions.
    if (literals.size() < d_conflictSize)
    {
      return TrustNode::null();
    }

    literals.resize(d_conflictSize);
    // Make cube from literals
    Node conj = NodeManager::currentNM()->mkAnd(literals);

    // For the strict-cube strategy, cubes look like the following:
    // C1 =             l1_{1} & .... & l1_{d_conflictSize}
    // C2 = !C1 &       l2_{1} & .... & l2_{d_conflictSize}
    // C3 = !C1 & !C2 & l3_{1} & .... & l3_{d_conflictSize}
    // C4 = !C1 & !C2 & !C3
    if (strict)
    {
      vector<Node> toEmit;
      for (const Node& c : d_cubes)
      {
        toEmit.push_back(c.notNode());
      }
      toEmit.push_back(conj);
      Node strict_cube = NodeManager::currentNM()->mkAnd(toEmit);
      d_strict_cubes.push_back(strict_cube);

      if (emitZLL)
      {
        // just increment and don't actually output the cube yet
        d_numPartitionsSoFar++;
      }
      else
      {
        emitCube(strict_cube);
      }
    }
    else
    {
      if (emitZLL)
      {
        // just increment and don't actually output the cube yet
        d_numPartitionsSoFar++;
      }
      else
      {
        emitCube(conj);
      }
    }
    // Add to the list of cubes.
    d_cubes.push_back(conj);
    return blockPath(conj);
  }
  // At the last cube
  else
  {
    if (emitZLL)
    {
      std::vector<Node> zllLiterals =
          d_propEngine->getLearnedZeroLevelLiterals(modes::LEARNED_LIT_INPUT);
      std::vector<Node>* cubes = strict ? &d_strict_cubes : &d_cubes;

      for (const auto& c : *cubes)
      {
        zllLiterals.push_back(c);
        Node lemma = NodeManager::currentNM()->mkAnd(zllLiterals);
        emitCube(lemma);
        zllLiterals.pop_back();
      }
    }

    vector<Node> nots;
    for (const Node& c : d_cubes)
    {
      nots.push_back(c.notNode());
    }
    Node lemma = NodeManager::currentNM()->mkAnd(nots);
    // Emit not(cube_one) and not(cube_two) and ... and not(cube_n-1)
    if (emitZLL)
    {
      std::vector<Node> zllLiterals =
          d_propEngine->getLearnedZeroLevelLiterals(modes::LEARNED_LIT_INPUT);
      zllLiterals.push_back(lemma);
      Node zllLemma = NodeManager::currentNM()->mkAnd(zllLiterals);
      emitCube(zllLemma);
    }
    else
    {
      emitCube(lemma);
    }
    return stopPartitioning();
  }
}

TrustNode PartitionGenerator::makeFullTrailPartitions(LiteralListType litType,
                                                      bool emitZLL)
{
  std::vector<Node> literals = collectLiterals(litType);
  uint64_t numVar = static_cast<uint64_t>(log2(d_numPartitions));
  if (literals.size() >= numVar)
  {
    literals.resize(numVar);

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
        emitCube(zllConj);
      }
      else
      {
        emitCube(conj);
      }
    }
    return stopPartitioning();
  }
  return TrustNode::null();
}

TrustNode PartitionGenerator::check(Theory::Effort e)
{
  if ((options().parallel.partitionCheck == options::CheckMode::FULL
       && !Theory::fullEffort(e))
      || (options().parallel.partitionCheck == options::CheckMode::STANDARD
          && Theory::fullEffort(e))
      || (options().parallel.computePartitions < 2))
  {
    return TrustNode::null();
  }

  auto now = std::chrono::steady_clock::now();
  std::chrono::duration<double> elapsedTime = now - d_startTime;
  bool timeLimitExceeded =
      elapsedTime.count() >= options().parallel.partitionTimeLimit;

  d_numChecks = d_numChecks + 1;
  d_betweenChecks = d_betweenChecks + 1;
  bool checkLimitExceeded =
      ((d_emittedAnyPartitions
        && d_betweenChecks >= options().parallel.checksBetweenPartitions)
       || (!d_emittedAnyPartitions
           && d_numChecks >= options().parallel.checksBeforePartitioning));

  switch (options().parallel.partitionWhen)
  {
    case options::PartitionWhenMode::TLIMIT:
    {
      if (!timeLimitExceeded)
      {
        return TrustNode::null();
      }
      // Otherwise, we partition.
      break;
    }
    case options::PartitionWhenMode::CLIMIT:
    {
      if (!checkLimitExceeded)
      {
        return TrustNode::null();
      }
      break;
    }
    case options::PartitionWhenMode::TLIMIT_CBACKUP:
    {
      if (!checkLimitExceeded)
      {
        if (!timeLimitExceeded)
        {
          return TrustNode::null();
        }
      }
      break;
    }
    case options::PartitionWhenMode::CLIMIT_TBACKUP:
    {
      if (!timeLimitExceeded)
      {
        if (!checkLimitExceeded)
        {
          return TrustNode::null();
        }
      }
      break;
    }
  }

  // Reset betweenChecks
  d_betweenChecks = 0;

  bool emitZLL = options().parallel.appendLearnedLiteralsToCubes;
  switch (options().parallel.partitionStrategy)
  {
    case options::PartitionMode::HEAP_CUBES:
      return makeFullTrailPartitions(/*litType=*/HEAP, emitZLL);
    case options::PartitionMode::DECISION_CUBES:
      return makeFullTrailPartitions(/*litType=*/DECISION, emitZLL);
    case options::PartitionMode::LEMMA_CUBES:
      return makeFullTrailPartitions(/*litType=*/LEMMA, emitZLL);
    case options::PartitionMode::STRICT_CUBE:
      return makeRevisedPartitions(/*strict=*/true, emitZLL);
    case options::PartitionMode::REVISED:
      return makeRevisedPartitions(/*strict=*/false, emitZLL);
    default: return TrustNode::null();
  }
}

}  // namespace theory
}  // namespace cvc5::internal
