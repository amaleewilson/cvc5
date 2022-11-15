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

#include <algorithm>

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
      d_emittedCubes(false)
{
  d_valuation = std::make_unique<Valuation>(theoryEngine);
  d_propEngine = propEngine;

  d_conflictSize = options().parallel.partitionConflictSize;
  if (!d_conflictSize)
  {
    d_conflictSize = static_cast<uint64_t>(log2(d_numPartitions));
  }
}

bool PartitionGenerator::emittedCubes() { return d_emittedCubes; }

void PartitionGenerator::addLemmaLiteral(TrustNode toAdd)
{
  // std::cout << "addinglemma literl" << std::endl;
  Node n = toAdd.getNode();
  Node originalN = SkolemManager::getOriginalForm(n);
  Node original = originalN.getKind() == kind::NOT ? originalN[0] : originalN;

  // TODO: will need to rework how we track nodes, but can do that later.
  // May be able to maintain a list of node IDs, find the most frequent,
  // and then somehow get by id.
  std::vector<Node> nodes;

  size_t len = original.getNumChildren();
  for (int i = 0; i < len; ++i)
  {
    d_lemmaLiterals.insert(original[i]);

    Node cn = original[i];
    if (d_lemmaMap.count(cn) == 1)
    {
      d_lemmaMap.insert_or_assign(cn, d_lemmaMap[cn] + 1);
    }
    else
    {
      d_lemmaMap.insert({cn, 1});
    }
    // std::cout << originalN[i] << std::endl;
    // std::cout << originalN[i].getId() << std::endl;
  }
  // std::cout << "toAdd " << std::endl;

  // if (originalN.getKind() == kind::NOT)
  // {
  //   std::cout << "NOT" << std::endl;
  // }
  // else if (originalN.getKind() == kind::OR)
  // {
  //   std::cout << "OR" << std::endl;
  // }
  // else if (originalN.getKind() == kind::AND)
  // {
  //   std::cout << "AND" << std::endl;
  // }
  // else
  // {
  //   std::cout << "toAdd (lemma literal) = " << originalN << std::endl;
  // }
}

std::vector<Node> PartitionGenerator::collectLiterals(LiteralListType litType)
{
  std::vector<Node> filteredLiterals;
  std::vector<Node> unfilteredLiterals;

  // Filter out the types of literals we don't want.
  // Make sure the literal does not have a boolean term or skolem in it.
  const std::unordered_set<Kind, kind::KindHashFunction> kinds = {
      kind::SKOLEM, kind::BOOLEAN_TERM_VARIABLE};

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
    case ZLL:
    {
      unfilteredLiterals =
          d_propEngine->getLearnedZeroLevelLiterals(modes::LEARNED_LIT_INPUT);
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
    default: return filteredLiterals;
  }

  if (litType == LEMMA)
  {
    // std::cout << "sorting lemma literals" << std::endl;
    // Sort based on d_lemmaMap
    std::sort(unfilteredLiterals.begin(),
              unfilteredLiterals.end(),
              [this](Node a, Node b) -> bool {
                return d_lemmaMap[a] > d_lemmaMap[b];
              });
    // for (auto f : unfilteredLiterals)
    // {
    //   std::cout << "id: " << f.getId() << " , count: " << d_lemmaMap[f]
    //             << std::endl;
    // }
    return unfilteredLiterals;
  }
  else if (litType == HEAP || litType == DECISION)
  {
    for (const Node& n : unfilteredLiterals)
    {
      Node originalN = SkolemManager::getOriginalForm(n);
      modes::LearnedLitType nType = d_propEngine->getLiteralType(n);

      // If the literal is the not of some node, do the checks for the child
      // of the not instead of the not itself.
      Node original =
          originalN.getKind() == kind::NOT ? originalN[0] : originalN;

      // std::cout << "node ID " << original.getId() << std::endl;
      // if (expr::hasSubtermKinds(kinds, original))
      // {
      //   std::cout << "subterm" << std::endl;
      // }
      // if (original.getKind() == kind::BOOLEAN_TERM_VARIABLE)
      // {
      //   std::cout << "booltermvar" << std::endl;
      // }
      // if (original.getKind() == kind::CONST_BOOLEAN)
      // {
      //   std::cout << "const bool" << std::endl;
      // }
      // if (!d_valuation->isSatLiteral(original))
      // {
      //   std::cout << "not sat literl" << std::endl;
      // }
      // if (Theory::theoryOf(original) == THEORY_BOOL)
      // {
      //   std::cout << "theory bool" << std::endl;
      // }
      // if (n.isConst())
      // {
      //   std::cout << "n is const" << std::endl;
      // }
      // if ((nType != modes::LEARNED_LIT_INPUT))
      // {
      //   std::cout << " not learned lit input type" << std::endl;
      // }
      // segfault????
      // if (!d_valuation->isDecision(original))
      // {
      //   std::cout << "not decision" << std::endl;
      // }

      // Ideally we use learned_lit_input as a first pass,
      // but if not then we don't use that filter.
      // ! - just make it a priority thing, rather than a filter.
      // See if you can meet Andy this week.
      // Partitioner that always succeeds no matter what (unless solved)

      // Things we want:
      //  - partition fast
      //  - succeed at partitioning

      // should be a traversal mechanism for getting the leaves/literals.

      // Ask Andy about priority vs things we should never use in partitions.

      // TODO: make theory_bool optional,
      // figure out why we still sometimes fail to partition.
      if (expr::hasSubtermKinds(kinds, original)
          || original.getKind() == kind::BOOLEAN_TERM_VARIABLE
          || original.getKind() == kind::CONST_BOOLEAN
          || !d_valuation->isSatLiteral(original)
          || Theory::theoryOf(original) == THEORY_BOOL || n.isConst()
          || (nType != modes::LEARNED_LIT_INPUT)
          // || !d_valuation->isDecision(original)
      )
      {
        continue;
      }
      filteredLiterals.push_back(originalN);
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
    d_emittedCubes = true;
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
    // of with 2^numVar variable so that each row can be emitted as a partition
    // later. Each entry in resultNodeLists is a row corresponding to a cube:
    // resultNodeLists = {
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
    // For the first column, numConsecutiveTF = 4, then 2 for the second column,
    // and 1 for the third column.
    size_t numConsecutiveTF = total / 2;
    for (Node n : literals)
    {
      Node not_n = n.notNode();

      // loc tracks which row/cube we're on
      size_t loc = 0;
      for (size_t z = 0; z < total / numConsecutiveTF; ++z)
      {
        t = !t;
        for (size_t j = 0; j < numConsecutiveTF; ++j)
        {
          resultNodeLists[loc].push_back(t ? n : not_n);
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
    d_emittedCubes = true;
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

  d_numChecks = d_numChecks + 1;
  d_betweenChecks = d_betweenChecks + 1;

  if (d_numChecks < options().parallel.checksBeforePartitioning
      || d_betweenChecks < options().parallel.checksBetweenPartitions)
  {
    return TrustNode::null();
  }

  // Reset betweenChecks
  d_betweenChecks = 0;

  bool emitZLL = options().parallel.appendLearnedLiteralsToCubes;
  switch (options().parallel.partitionStrategy)
  {
    case options::PartitionMode::HEAP_TRAIL:
      return makeFullTrailPartitions(/*litType=*/HEAP, emitZLL);
    case options::PartitionMode::DECISION_TRAIL:
      return makeFullTrailPartitions(/*litType=*/DECISION, emitZLL);
    case options::PartitionMode::STRICT_CUBE:
      return makeRevisedPartitions(/*strict=*/true, emitZLL);
    case options::PartitionMode::REVISED:
      return makeRevisedPartitions(/*strict=*/false, emitZLL);
    case options::PartitionMode::LEMMA_CUBES:
      return makeFullTrailPartitions(/*litType=*/LEMMA, emitZLL);
    default: return TrustNode::null();
  }
}

}  // namespace theory
}  // namespace cvc5::internal
