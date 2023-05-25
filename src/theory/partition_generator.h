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

#include "cvc5_private.h"

#ifndef CVC5__THEORY__SPLITTER_H
#define CVC5__THEORY__SPLITTER_H

#include <chrono>
#include <unordered_map>
#include <vector>

#include "proof/trust_node.h"
#include "smt/env_obj.h"
#include "theory/theory.h"
#include "theory/valuation.h"

namespace cvc5::internal {

class TheoryEngine;

namespace prop {
class PropEngine;
}

namespace theory {

class PartitionGenerator : protected EnvObj
{
 public:
  PartitionGenerator(Env& env,
                     TheoryEngine* theoryEngine,
                     prop::PropEngine* propEngine);

  /**
   * Make partitions for parallel solving. e communicates the effort at which
   * check was called. Returns a lemma blocking off the emitted cube from the
   * search.
   */
  TrustNode check(Theory::Effort e);

  /**
   * Add the literals from the toAdd Node to our list of literals from lemmas.
   */
  void addLemmaLiteral(TrustNode toAdd);

  /**
   * Emit any pending partitions that were not emitted during solving.
   */
  void emitPendingPartitions(bool solved);

 private:
  /* LiteralListType is used to specify where to pull literals from when calling
   * collectLiterals. HEAP for the order_heap in the SAT solver, DECISION for
   * the decision trail in the SAT solver, and ZLL for the zero-level learned
   * literals.
   */
  enum LiteralListType
  {
    HEAP,
    DECISION,
    LEMMA,
    ZLL
  };
  /**
   * Increment d_numPartitionsSoFar and print the cube to 
   * the output file specified by --write-partitions-to. 
   */
  void emitPartition(Node toEmit);

  /**
   * Partition using the "revised" strategy, which emits cubes such as C1, C2,
   * C3, !C1 & !C2 & !C3. If strict is set to true, a modified version of this
   * emits "strict cubes:" C1, !C1 & C2, !C1 & !C2 & C3, !C1 & !C2 & !C3. If
   * emitZLL is set to true, then zero-level learned literals will be appended
   * to the cubes.
   */
  TrustNode makeDisjointNonCubePartitions(LiteralListType litType,
                                          bool emitZLL,
                                          bool timedOut,
                                          bool useTrailTail,
                                          bool randomize);

  /**
   * Partition by taking a list of literals and emitting mutually exclusive
   * cubes that resemble entries in a truth table: 
   * C1: { l1, !l2}
   * C2: { l1,  l2}
   * C3: {!l1, !l2}
   * C4: {!l1,  l2}
   * If emitZLL is set to true, then zero-level learned literals will be
   * appended to the cubes.
   */
  TrustNode makeCubePartitions(LiteralListType litType,
                               bool emitZLL,
                               bool useTrailTail,
                               bool randomize);

  /**
   * Generate a lemma that is the negation of toBlock which ultimately blocks
   * that path in the search.
   */
  TrustNode blockPath(TNode toBlock);

  /**
   * Stop partitioning and return unsat.
   */
  TrustNode stopPartitioning();

  /**
   * Get a list of literals.
   * litType specifies whether to pull from the decision trail in the sat solver,
   * from the order heap in the sat solver, or from the zero level learned literals.
   */
  std::vector<Node> collectLiterals(LiteralListType litType);

/**
 * Returns the d_cubes, the cubes that have been created for partitioning the
 * original problem.
 */

std::vector<Node> getPartitions() const { return d_cubes; }

/**
 * Apply the priority heuristic to the set of literals.
 */
void usePriorityHeuristic(std::vector<Node>& unfilteredLiterals,
                          std::vector<Node>& filteredLiterals);

/**
 * Check if we can use the literal/var represented by node.
 */
bool isUnusable(Node n);

/**
 * The time point when this partition generator was instantiated, used to
 * compute elapsed time.
 */
std::chrono::time_point<std::chrono::steady_clock> d_startTime;

/**
 * Used to track the inter-partition time.
 */
std::chrono::time_point<std::chrono::steady_clock>
    d_startTimeOfPreviousPartition;

/**
 * Current propEngine.
 */
prop::PropEngine* d_propEngine;

/**
 * Valuation of the theory engine.
 */
std::unique_ptr<Valuation> d_valuation;

/**
 * The number of partitions requested through the compute-partitions option.
 */
const uint64_t d_numPartitions;

/**
 * Number of standard or full (depending on partition check mode) checks that
 * have occured.
 */
uint64_t d_numChecks;

/**
 * Number of standard checks that have occured since the last partition that was emitted. 
 */
uint64_t d_betweenChecks;

/**
 * The number of partitions that have been created.
 */
uint64_t d_numPartitionsSoFar;

/**
 * Lemmas that have been sent to the SAT solver.
 */
std::vector<Node> d_assertedLemmas;

/**
 * List of the cubes that have been created.
 */
std::vector<Node> d_cubes;

/**
 * List of the strict cubes that have been created.
 */
std::vector<Node> d_dncs;

/**
 * Minimum number of literals required in the list of decisions for cubes to
 * be made.
 */
uint64_t d_conflictSize;

/**
 * Track whether any partitions have been emitted.
 */
bool d_createdAnyPartitions;

/**
 * Track whether any partitions have been emitted.
 */
bool d_emittedAllPartitions;

/**
 * Track lemma literals that we have seen and their frequency.
 */
std::unordered_map<Node, int> d_lemmaMap;

/**
 * Track lemma literals we have seen.
 */
std::set<Node> d_lemmaLiterals;

/**
 * Track lemma literals we have used in DNCs.
 */
std::set<Node> d_usedLemmaLiterals;
};
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__PARTITION__GENERATOR_H */
