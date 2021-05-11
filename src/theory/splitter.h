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
 * The trust node utility.
 */

#include <list>

#include "cvc5_private.h"
#include "theory/valuation.h"

#ifndef CVC5__THEORY__SPLITTER_H
#define CVC5__THEORY__SPLITTER_H

#include "expr/node.h"

// TODO: remove unneccessary incluedes

#include "base/check.h"
#include "context/cdhashmap.h"
#include "expr/node.h"
#include "options/theory_options.h"
#include "theory/atom_requests.h"
#include "theory/engine_output_channel.h"
#include "theory/interrupted.h"
#include "theory/rewriter.h"
#include "theory/sort_inference.h"
#include "theory/splitter.h"
#include "theory/theory.h"
#include "theory/theory_preprocessor.h"
#include "theory/trust_node.h"
#include "theory/trust_substitutions.h"
#include "theory/uf/equality_engine.h"
#include "theory/valuation.h"
#include "util/hash.h"
#include "util/statistics_stats.h"
#include "util/unsafe_interrupt_exception.h"

namespace cvc5 {

class TheoryEngine;

namespace theory {

class Splitter
{
 public:
  Splitter(TheoryEngine* theoryEngine) : d_numPartition(0)
  {
    d_valuation = std::make_unique<Valuation>(theoryEngine);
  }
  TrustNode makePartitions();

 private:
  std::unique_ptr<Valuation> d_valuation;
  int d_numPartition;
  std::list<Node> d_asertedPartitions;
};
}  // namespace theory
}  // namespace cvc5

#endif /* CVC5__THEORY__SPLITTER_H */
