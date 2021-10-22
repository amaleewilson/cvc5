/*
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
 * The trust node utility.
 */

#include "theory/splitter.h"

#include <math.h>

#include "expr/node_algorithm.h"
#include "expr/node_builder.h"
#include "theory/theory_engine.h"
#include "theory/theory_id.h"
#include "theory/theory_traits.h"

using namespace std;
using namespace cvc5::theory;

namespace cvc5 {

namespace theory {

// TODO: if we get too many, just write the previous level
// if too fine grained, output the most fine grained still
// in your threshold.
TrustNode Splitter::makePartitions()
{
  if (d_partitionFile != "")
  {
    d_partitionFileStream.open(d_partitionFile, std::ios_base::app);
    d_output = &d_partitionFileStream;
  }

  // You really just want to stop here.
  // You broke this by asking for 2 partitions. 


  if (d_numPartitionsSoFar == d_numPartitions - 1)
  {
    if (d_numPartitionsSoFar == 1) {
      
    }
    // added cubes: C1, C2, C3
    // asserted lemmas: -C1 /\ -C2 /\ -C3

    // now add cube: -C1 \/ -C2 \/ -C3
    // now assert lemma: -(-C1 /\ -C2 /\ -C3)

    // 10/19/21
    // ask for 4 cubes
    // Cubes C1, C2, C3, C4: C1 = -C1, C2 = -C2, C3 = -C3, C4 = C1 \/ C2 \/ C3

    // Last partition
    // Dump and assert the negation of the previous cubes

    NodeBuilder orBuilder(kind::OR);
    // make a trustnode of everything in lst and call conflict.
    for (const auto d : d_assertedLemmas) orBuilder << d;
    for (const auto d : d_assertedLemmas) std::cout << "OR'ing " << d << std::endl;
    if (d_assertedLemmas.size() == 1){
      std::cout << "above forced to OR with itself" << std::endl;
      orBuilder << d_assertedLemmas.front();
    }

    Node disj = orBuilder.constructNode();

    // std::cout << "Last cube" << std::endl;
    *d_output << disj << "\n";
    // std::cout << disj << "\n";
    // append to list after creating.
    if (d_partitionFile != "")
    {
      d_partitionFileStream.close();
    }

    // return a mktrust of false.
    NodeBuilder andBuilder(kind::AND);
    // make a trustnode of everything in lst and call conflict.
    for (const auto d : d_assertedLemmas) andBuilder << d;
    for (const auto d : d_assertedLemmas) std::cout << "AND'ing " << d << std::endl;
    if (d_assertedLemmas.size() == 1){
      std::cout << "above forced to AND with itself" << std::endl;
      andBuilder << d_assertedLemmas.front();
    }
    Node conj = andBuilder.constructNode();
    NodeBuilder notBuilder(kind::NOT);
    notBuilder << conj;
    Node lemma = notBuilder.constructNode();

    return TrustNode::mkTrustLemma(lemma);
  }
  else
  {
    std::vector<TNode> literals;
    for (TheoryId theoryId = THEORY_FIRST; theoryId < THEORY_LAST; ++theoryId)
    {
      // if (!logicInfo.isTheoryEnabled(theoryId))
      // {
      // continue;
      // }
      for (context::CDList<Assertion>::const_iterator
               it = d_valuation->factsBegin(theoryId),
               it_end = d_valuation->factsEnd(theoryId);
           it != it_end;
           ++it)
      {
        TNode a = (*it).d_assertion;
        if (d_valuation->isSatLiteral(a) && d_valuation->isDecision(a))
        {
          // have a mapping of nodes to whether they qualify for the list.
          // TODO: Revisit this bool_term_var thing.
          Node og = SkolemManager::getOriginalForm(a);
          std::unordered_set<Kind, kind::KindHashFunction> kinds = {
              kind::SKOLEM, kind::BOOLEAN_TERM_VARIABLE};
          // convert to original form
          if (expr::hasSubtermKinds(kinds, og)) continue;
          // useful debug
          // std::cout << "skolem" << a << std::endl;
          literals.push_back(og);
        }
      }
    }

    /*
    If we don't emit any conflict, then the result is valid.
    completely naive way: this entire feature is finding one literal
    Split on it and recurse at the higher level.
    Does gg know which partitions are free?
    For any given problem, try solving it directly and also produce splits to
    try on other machines.
    Can this be made adaptive?
    Need to be able to make just one partition.
    */
    unsigned conflictSize = (unsigned)log2(d_numPartitions);
    if (literals.size() >= conflictSize)
    {
      // make a trustnode of everything in lst and call conflict.
      std::vector<Node> tmpLiterals(literals.begin(),
                                    literals.begin() + conflictSize);
      Node conj = NodeManager::currentNM()->mkAnd(tmpLiterals);
      // std::cout << "Not last cube" << std::endl;
      *d_output << conj << "\n";
      if (d_partitionFile != "")
      {
        d_partitionFileStream.close();
      }

      // std::cout << conj << "\n";
      // NodeBuilder andBuilder(kind::AND);
      // for (auto d : literals) andBuilder << d;
      // Node conj = andBuilder.constructNode();
      NodeBuilder notBuilder(kind::NOT);
      notBuilder << conj;
      Node lemma = notBuilder.constructNode();

      ++d_numPartitionsSoFar;
      d_assertedLemmas.push_back(lemma);

      TrustNode trustedLemma = TrustNode::mkTrustLemma(lemma);
      return trustedLemma;
    }
  }

  if (d_partitionFile != "")
  {
    d_partitionFileStream.close();
  }

  return TrustNode::null();
}

}  // namespace theory
}  // namespace cvc5
