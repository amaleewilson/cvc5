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

#ifndef CVC5__THEORY__SPLITTER_H
#define CVC5__THEORY__SPLITTER_H

#include <fstream>
#include <list>
#include <sstream>

#include "options/smt_options.h"
#include "theory/trust_node.h"
#include "theory/valuation.h"

namespace cvc5 {

class TheoryEngine;

namespace theory {

class Splitter
{
 public:
  Splitter(TheoryEngine* theoryEngine)
      : d_numPartitions(options::computePartitions())
      , d_numPartitionsSoFar(0)
      , d_partitionFile(options::writePartitionsToFileName())
  {
    Assert(numPartitions > 1);
    d_valuation = std::make_unique<Valuation>(theoryEngine);
    std::ofstream output;
    output.open (d_partitionFile);
    output.close();
  }
  TrustNode makePartitions();

 private:
  std::unique_ptr<Valuation> d_valuation;
  const unsigned d_numPartitions;
  unsigned d_numPartitionsSoFar;
  std::string d_partitionFile;
  std::list<Node> d_asertedPartitions;
};
}  // namespace theory
}  // namespace cvc5

#endif /* CVC5__THEORY__SPLITTER_H */
