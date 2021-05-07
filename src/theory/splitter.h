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

#include "cvc5_private.h"

#include <list>

#include "theory/valuation.h"

#ifndef CVC5__THEORY__SPLITTER_H
#define CVC5__THEORY__SPLITTER_H

#include "expr/node.h"

namespace cvc5 {

class TheoryEngine;

namespace theory {

class Splitter
{
 public:
    Splitter(TheoryEngine* theoryEngine)
        : d_numPartition(0)
    {
        d_valuation = std::make_unique<Valuation>(theoryEngine);
    }


 private:
    std::unique_ptr<Valuation> d_valuation;
    int d_numPartition;
    std::list<Node> d_asertedPartitions;
};
}  // namespace theory
}  // namespace cvc5

#endif /* CVC5__THEORY__SPLITTER_H */
