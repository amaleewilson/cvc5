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

#include <sstream>
#include <fstream>

#include "base/map_util.h"
#include "decision/decision_engine.h"
#include "expr/attribute.h"
#include "expr/lazy_proof.h"
#include "expr/node_algorithm.h"
#include "expr/node_builder.h"
#include "expr/node_visitor.h"
#include "expr/proof_checker.h"
#include "expr/proof_ensure_closed.h"
#include "options/quantifiers_options.h"
#include "options/theory_options.h"
#include "printer/printer.h"
#include "prop/prop_engine.h"
#include "smt/dump.h"
#include "smt/logic_exception.h"
#include "smt/output_manager.h"
#include "theory/combination_care_graph.h"
#include "theory/decision_manager.h"
#include "theory/quantifiers/first_order_model.h"
#include "theory/quantifiers_engine.h"
#include "theory/relevance_manager.h"
#include "theory/rewriter.h"
#include "theory/shared_solver.h"
#include "theory/theory.h"
#include "theory/theory_engine.h"
#include "theory/theory_engine_proof_generator.h"
#include "theory/theory_id.h"
#include "theory/theory_model.h"
#include "theory/theory_traits.h"
#include "theory/uf/equality_engine.h"
#include "util/resource_manager.h"

namespace cvc5 {

namespace theory {

TrustNode Splitter::makePartitions()
{
  int numPartitions = options::computePartition();
  Assert(numPartitions > 1);

  /*
 x1 = 1
 x2 > 2
 lemma a: !(x1 = 1 /\ x2 > 2)

 x1 = 2
 x2 < 2
 lemma b: !(x1 = 2 /\ x2 < 2)

 !(a /\ b)

 a \/ b \/ (-a \/ -b)
  */

  std::ofstream output;
  output.open (d_partitionFile, std::ofstream::app);

  if (d_numPartition == numPartitions - 1)
  {
    // Dump and assert the negation of the previous cubes
    Node c = *d_asertedPartitions.begin();
    if (d_asertedPartitions.size() > 1)
    {
      NodeBuilder nb(kind::AND);
      // make a trustnode of everything in lst and call conflict.
      for (const auto d : d_asertedPartitions)
      {
        nb << d;
      }
      c = nb.constructNode();
    }
    NodeBuilder nb2(kind::NOT);
    nb2 << c;
    Node l = nb2.constructNode();
    // std::cout << l << std::endl;

    // Last partition
    TrustNode tl = TrustNode::mkTrustLemma(l);
    // std::cout << tl << std::endl;

    output << l << "\n";
    output.close();
    return tl;
  }
  else
  {
    std::vector<TNode> lst;
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
        if (d_valuation->isSatLiteral(a))
        {
          if (d_valuation->isDecision(a))
          {
            // Revisit this bool_term_var thing.
            if (expr::hasSubtermKind(kind::BOOLEAN_TERM_VARIABLE, a))
            {
              // useful debug
              // std::cout << "bool term " << a << std::endl;
            }
            if (expr::hasSubtermKind(kind::SKOLEM, a))
            {
              // convert to original form
              // push orignal form to lst.
              Node og = SkolemManager::getOriginalForm(a);
              // useful debug
              // std::cout << "skolem" << a << std::endl;
              lst.push_back(og);
            }
            else
            {
              // just push original form to list.
              // useful debug
              // std::cout << "other " << a << std::endl;
              lst.push_back(a);
            }
          }
        }
      }
    }

    // useful debug
    // for (auto thing : lst) {
    //   std::cout << "thing in list " << thing << std::endl;
    // }

    if (!lst.empty())
    {
      Node c = *lst.begin();
      if (lst.size() > 1)
      {
        NodeBuilder nb(kind::AND);
        // make a trustnode of everything in lst and call conflict.
        for (auto d : lst)
        {
          nb << d;
        }
        c = nb.constructNode();
      }
      NodeBuilder nb2(kind::NOT);
      nb2 << c;
      Node l = nb2.constructNode();
      //std::cout << l << std::endl;

      ++d_numPartition;
      d_asertedPartitions.push_back(l);

      /*
      NodeManager * nm = NodeManager::currentNM();
      Node c = nm->mkNot(*lst.begin());
    if (lst.size() > 1)
    {
        c = nm->mkAnd(lst);
        c = nm->mkNot(c);
    }
      */

      TrustNode tl = TrustNode::mkTrustLemma(l);
      // std::cout << lst.size() << std::endl;
      // std::cout << tl << std::endl;
      // Node c = (Node)nb;
      // conflict(tc, THEORY_BUILTIN);
      // lemma(tl, LemmaProperty::NONE, THEORY_LAST, THEORY_BUILTIN );
      output << l << "\n";
      output.close();
      return tl;
    }
  }

  return TrustNode::null();
}

}  // namespace theory
}  // namespace cvc5
