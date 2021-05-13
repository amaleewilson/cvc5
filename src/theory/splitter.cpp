/******************************************************************************
 * Top contributors (to current version):
    Amalee Wilson, Andrew Wu
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

#include "expr/node_algorithm.h"
#include "expr/node_builder.h"
#include "theory/theory_engine.h"
#include "theory/theory_id.h"
#include "theory/theory_traits.h"

namespace cvc5 {

namespace theory {

TrustNode Splitter::makePartitions()
{
  std::ofstream output;
  output.open (d_partitionFile, std::ofstream::app);

  if (d_numPartitionsSoFar == d_numPartitions - 1)
  {
    // Last partition
    // Dump and assert the negation of the previous cubes
    NodeBuilder andBuilder(kind::AND);
    // make a trustnode of everything in lst and call conflict.
    for (const auto d : d_asertedPartitions)
        andBuilder << d;
    Node conj = andBuilder.constructNode();
    NodeBuilder notBuilder(kind::NOT);
    notBuilder << conj;
    Node lemma = notBuilder.constructNode();

    output << lemma << "\n";
    output.close();
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
          // TODO: Revisit this bool_term_var thing.
          std::unordered_set<Kind, kind::KindHashFunction> kinds =
              {kind::SKOLEM, kind::BOOLEAN_TERM_VARIABLE};
          if (expr::hasSubtermKinds(kinds, a))
          {
            // convert to original form
            Node og = SkolemManager::getOriginalForm(a);
            if ( expr::hasSubtermKinds(kinds, og) )
              continue;
            // useful debug
            // std::cout << "skolem" << a << std::endl;
            literals.push_back(og);
          }
          else
          {
            // just push original form to list.
            // useful debug
            // std::cout << "other " << a << std::endl;
            literals.push_back(a);
          }
        }
      }
    }

    // useful debug
    // for (auto thing : lst) {
    //   std::cout << "thing in list " << thing << std::endl;
    // }

    if (!literals.empty())
    {
      // make a trustnode of everything in lst and call conflict.
      NodeBuilder andBuilder(kind::AND);
      for (auto d : literals)
        andBuilder << d;
      Node conj = andBuilder.constructNode();
      NodeBuilder notBuilder(kind::NOT);
      notBuilder << conj;
      Node lemma = notBuilder.constructNode();
      output << lemma << "\n";
      output.close();

      ++d_numPartitionsSoFar;
      d_asertedPartitions.push_back(lemma);

      TrustNode trustedLemma = TrustNode::mkTrustLemma(lemma);
      // std::cout << lst.size() << std::endl;
      // std::cout << tl << std::endl;
      // Node c = (Node)nb;
      // conflict(tc, THEORY_BUILTIN);
      // lemma(tl, LemmaProperty::NONE, THEORY_LAST, THEORY_BUILTIN );
      return trustedLemma;
    }
  }
  return TrustNode::null();
}

}  // namespace theory
}  // namespace cvc5
