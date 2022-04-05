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
using namespace cvc5::theory;

namespace cvc5 {

namespace theory {
PartitionGenerator::PartitionGenerator(Env& env,
                                       TheoryEngine* theoryEngine,
                                       prop::PropEngine* propEngine)
    : EnvObj(env),
      d_numPartitions(options().parallel.computePartitions),
      d_numChecks(0),
      d_numPartitionsSoFar(0)
{
  d_valuation = std::make_unique<Valuation>(theoryEngine);
  d_propEngine = propEngine;

  d_conflictSize = options().parallel.partitionConflictSize;
  if (!d_conflictSize)
  {
    d_conflictSize = static_cast<uint64_t>(log2(d_numPartitions));
  }
}

std::vector<TNode> PartitionGenerator::collectDecisionLiterals()
{
  std::vector<TNode> literals;
  std::vector<Node> decisionNodes;
  if (options().parallel.partitionStrategy
      == options::PartitionMode::HEAP_TRAIL)
  {
    decisionNodes = d_propEngine->getPropOrderHeap();
  }
  else
  {
    decisionNodes = d_propEngine->getPropDecisions();
  }

  // Make sure the literal does not have a boolean term or skolem in it.
  const std::unordered_set<Kind, kind::KindHashFunction> kinds = {
      kind::SKOLEM, kind::BOOLEAN_TERM_VARIABLE, kind::CONST_BOOLEAN};

  for (const Node& n : decisionNodes)
  {
    Node originalN = SkolemManager::getOriginalForm(n);

    // If the literal is the not of some node, do the checks for the child
    // of the not instead of the not itself.
    Node original = originalN.getKind() == kind::NOT ? originalN[0] : originalN;
    if (expr::hasSubtermKinds(kinds, original)
        || !d_valuation->isSatLiteral(original)
        || !d_valuation->isDecision(original)
        || Theory::theoryOf(original) == THEORY_BOOL)
    {
      continue;
    }

    literals.push_back(originalN);
  }
  return literals;
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
TrustNode PartitionGenerator::makeRevisedPartitions()
{
  // If we're not at the last cube
  if (d_numPartitionsSoFar < d_numPartitions - 1)
  {
    std::vector<TNode> literals = collectDecisionLiterals();

    // Make sure we have enough literals.
    // Conflict size can be set through options, but the default is log base 2
    // of the requested number of partitions.
    if (literals.size() < d_conflictSize)
    {
      return TrustNode::null();
    }

    literals.resize(d_conflictSize);
    // Make first cube and emit it.
    Node conj = NodeManager::currentNM()->mkAnd(literals);

    if (options().parallel.partitionStrategy
        == options::PartitionMode::STRICT_CUBE)
    {
      vector<Node> nots;
      for (auto c : d_cubes) nots.push_back(c.notNode());
      Node lemma = NodeManager::currentNM()->mkAnd(nots);

      std::vector<TNode> toConj = {conj, lemma};
      Node to_emit = NodeManager::currentNM()->mkAnd(toConj);
      emitCube(to_emit);
    }
    else
    {
      emitCube(conj);
    }

    // Add to the list of cubes.
    d_cubes.push_back(conj);
    return blockPath(conj);
  }
  // At the last cube
  else
  {
    vector<Node> nots;
    for (auto c : d_cubes) nots.push_back(c.notNode());
    Node lemma = NodeManager::currentNM()->mkAnd(nots);
    // Emit not(cube_one) and not(cube_two) and ... and not(cube_n-1)
    emitCube(lemma);
    return stopPartitioning();
  }
}

TrustNode PartitionGenerator::makeFullTrailPartitions()
{
  std::vector<TNode> literals = collectDecisionLiterals();
  uint64_t num_var = static_cast<uint64_t>(log2(d_numPartitions));
  if (literals.size() >= num_var)
  {
    literals.resize(num_var);
    std::vector<Node> part_nodes;
    int part_depth = num_var;

    // This complicated thing is basically making a truth table
    // of length 2^depth so that these can be put together into a partition
    // later.
    std::vector<std::vector<Node> > result_node_lists(pow(2, part_depth));
    std::vector<std::vector<std::string> > testv(pow(2, part_depth));
    bool t = false;
    int q = part_depth;
    for (Node n : literals)
    {
      NodeBuilder notBuilder(kind::NOT);
      notBuilder << n;
      Node lemma = notBuilder.constructNode();
      int total = pow(2, part_depth);
      q = q - 1;
      int loc = 0;
      for (int z = 0; z < total / pow(2, q); ++z)
      {
        t = !t;
        for (int j = 0; j < total; ++j)
        {
          if (j < pow(2, q))
          {
            result_node_lists[loc].push_back((t ? n : lemma));
            ++loc;
          }
        }
      }
    }
    for (std::vector<Node> lst : result_node_lists)
    {
      Node conj = NodeManager::currentNM()->mkAnd(lst);
      emitCube(conj);
    }
    return stopPartitioning();
  }
  return TrustNode::null();
}

TrustNode PartitionGenerator::makePartitions(Theory::Effort e)
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

  if (d_numChecks < options().parallel.checksBeforePartitioning)
  {
    return TrustNode::null();
  }

  switch (options().parallel.partitionStrategy)
  {
    case options::PartitionMode::REVISED: return makeRevisedPartitions();
    case options::PartitionMode::STRICT_CUBE: return makeRevisedPartitions();
    case options::PartitionMode::DECISION_TRAIL:
      return makeFullTrailPartitions();
    case options::PartitionMode::HEAP_TRAIL: return makeFullTrailPartitions();
    default: return TrustNode::null();
  }
}

}  // namespace theory
}  // namespace cvc5
