/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mudathir Mohamed, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Bags theory type rules.
 */

#include "theory/bags/theory_bags_type_rules.h"

#include <sstream>

#include "base/check.h"
#include "expr/dtype.h"
#include "expr/dtype_cons.h"
#include "expr/emptybag.h"
#include "theory/bags/bags_utils.h"
#include "theory/datatypes/project_op.h"
#include "theory/datatypes/tuple_utils.h"
#include "util/cardinality.h"
#include "util/rational.h"

namespace cvc5::internal {
namespace theory {
namespace bags {

using namespace datatypes;

TypeNode BinaryOperatorTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}
TypeNode BinaryOperatorTypeRule::computeType(NodeManager* nodeManager,
                                             TNode n,
                                             bool check,
                                             std::ostream* errOut)
{
  Assert(n.getKind() == Kind::BAG_UNION_MAX
         || n.getKind() == Kind::BAG_UNION_DISJOINT
         || n.getKind() == Kind::BAG_INTER_MIN
         || n.getKind() == Kind::BAG_DIFFERENCE_SUBTRACT
         || n.getKind() == Kind::BAG_DIFFERENCE_REMOVE);
  TypeNode bagType = n[0].getTypeOrNull();
  TypeNode secondBagType = n[1].getTypeOrNull();
  if (check)
  {
    if (!bagType.isBag())
    {
      if (errOut)
      {
        (*errOut) << "operator expects a bag, first argument is not";
      }
      return TypeNode::null();
    }
    if (secondBagType != bagType)
    {
      if (errOut)
      {
        (*errOut) << "Operator " << n.getKind()
                  << " expects two bags of the same type. Found types '"
                  << bagType << "' and '" << secondBagType << "'.";
      }
      return TypeNode::null();
    }
  }
  return bagType;
}

bool BinaryOperatorTypeRule::computeIsConst(NodeManager* nodeManager, TNode n)
{
  // only UNION_DISJOINT has a const rule in kinds.
  // Other binary operators do not have const rules in kinds
  Assert(n.getKind() == Kind::BAG_UNION_DISJOINT);
  return BagsUtils::isConstant(n);
}

TypeNode SubBagTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return nm->booleanType();
}
TypeNode SubBagTypeRule::computeType(NodeManager* nodeManager,
                                     TNode n,
                                     bool check,
                                     std::ostream* errOut)
{
  Assert(n.getKind() == Kind::BAG_SUBBAG);
  TypeNode bagType = n[0].getTypeOrNull();
  if (check)
  {
    if (!bagType.isMaybeKind(Kind::BAG_TYPE))
    {
      if (errOut)
      {
        (*errOut) << "BAG_SUBBAG operating on non-bag";
      }
      return TypeNode::null();
    }
    TypeNode secondBagType = n[1].getTypeOrNull();
    if (!secondBagType.isComparableTo(bagType))
    {
      if (errOut)
      {
        (*errOut) << "BAG_SUBBAG operating on bags of different types";
      }
      return TypeNode::null();
    }
  }
  return nodeManager->booleanType();
}

TypeNode CountTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return nm->integerType();
}
TypeNode CountTypeRule::computeType(NodeManager* nodeManager,
                                    TNode n,
                                    bool check,
                                    std::ostream* errOut)
{
  Assert(n.getKind() == Kind::BAG_COUNT);
  TypeNode bagType = n[1].getTypeOrNull();
  if (check)
  {
    if (!bagType.isBag())
    {
      if (errOut)
      {
        (*errOut) << "checking for membership in a non-bag";
      }
      return TypeNode::null();
    }
    TypeNode elementType = n[0].getTypeOrNull();
    // e.g. (bag.count 1 (bag (BagMakeOp Real) 1.0 3))) is 3 whereas
    // (bag.count 1.0 (bag (BagMakeOp Int) 1 3)) throws a typing error
    if (elementType != bagType.getBagElementType())
    {
      if (errOut)
      {
        (*errOut) << "member operating on bags of different types:\n"
                  << "child type:  " << elementType << "\n"
                  << "not type: " << bagType.getBagElementType() << "\n"
                  << "in term : " << n;
      }
      return TypeNode::null();
    }
  }
  return nodeManager->integerType();
}

TypeNode MemberTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return nm->booleanType();
}
TypeNode MemberTypeRule::computeType(NodeManager* nodeManager,
                                     TNode n,
                                     bool check,
                                     std::ostream* errOut)
{
  Assert(n.getKind() == Kind::BAG_MEMBER);
  TypeNode bagType = n[1].getTypeOrNull();
  if (check)
  {
    if (!bagType.isBag())
    {
      if (errOut)
      {
        (*errOut) << "checking for membership in a non-bag";
      }
      return TypeNode::null();
    }
    TypeNode elementType = n[0].getTypeOrNull();
    // e.g. (bag.member 1 (bag 1.0 1)) is true whereas
    // (bag.member 1.0 (bag 1 1)) throws a typing error
    if (elementType != bagType.getBagElementType())
    {
      if (errOut)
      {
        (*errOut) << "member operating on bags of different types:\n"
                  << "child type:  " << elementType << "\n"
                  << "not type: " << bagType.getBagElementType() << "\n"
                  << "in term : " << n;
      }
      return TypeNode::null();
    }
  }
  return nodeManager->booleanType();
}

TypeNode SetofTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}
TypeNode SetofTypeRule::computeType(NodeManager* nodeManager,
                                    TNode n,
                                    bool check,
                                    std::ostream* errOut)
{
  Assert(n.getKind() == Kind::BAG_SETOF);
  TypeNode bagType = n[0].getTypeOrNull();
  if (check)
  {
    if (!bagType.isBag())
    {
      if (errOut)
      {
        (*errOut) << "Applying BAG_SETOF on a non-bag argument in term " << n;
      }
      return TypeNode::null();
    }
  }
  return bagType;
}

TypeNode BagMakeTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}
TypeNode BagMakeTypeRule::computeType(NodeManager* nm,
                                      TNode n,
                                      bool check,
                                      std::ostream* errOut)
{
  Assert(n.getKind() == Kind::BAG_MAKE);
  TypeNode actualElementType = n[0].getTypeOrNull();
  if (check)
  {
    if (n.getNumChildren() != 2)
    {
      if (errOut)
      {
        (*errOut) << "operands in term " << n << " are " << n.getNumChildren()
                  << ", but BAG_MAKE expects 2 operands.";
      }
      return TypeNode::null();
    }
    TypeNode type1 = n[1].getTypeOrNull();
    if (!type1.isInteger())
    {
      if (errOut)
      {
        (*errOut) << "BAG_MAKE expects an integer for " << n[1] << ". Found"
                  << type1;
      }
      return TypeNode::null();
    }
  }

  return nm->mkBagType(actualElementType);
}

bool BagMakeTypeRule::computeIsConst(NodeManager* nodeManager, TNode n)
{
  Assert(n.getKind() == Kind::BAG_MAKE);
  // for a bag to be a constant, both the element and its multiplicity should
  // be constants, and the multiplicity should be > 0.
  return n[0].isConst() && n[1].isConst()
         && n[1].getConst<Rational>().sgn() == 1;
}

TypeNode EmptyBagTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}
TypeNode EmptyBagTypeRule::computeType(NodeManager* nodeManager,
                                       TNode n,
                                       bool check,
                                       std::ostream* errOut)
{
  Assert(n.getKind() == Kind::BAG_EMPTY);
  EmptyBag emptyBag = n.getConst<EmptyBag>();
  return emptyBag.getType();
}

TypeNode CardTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return nm->integerType();
}
TypeNode CardTypeRule::computeType(NodeManager* nodeManager,
                                   TNode n,
                                   bool check,
                                   std::ostream* errOut)
{
  Assert(n.getKind() == Kind::BAG_CARD);
  TypeNode bagType = n[0].getTypeOrNull();
  if (check)
  {
    if (!bagType.isBag())
    {
      if (errOut)
      {
        (*errOut) << "cardinality operates on a bag, non-bag object found";
      }
      return TypeNode::null();
    }
  }
  return nodeManager->integerType();
}

TypeNode ChooseTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}
TypeNode ChooseTypeRule::computeType(NodeManager* nodeManager,
                                     TNode n,
                                     bool check,
                                     std::ostream* errOut)
{
  Assert(n.getKind() == Kind::BAG_CHOOSE);
  TypeNode bagType = n[0].getTypeOrNull();
  if (check)
  {
    if (!bagType.isBag())
    {
      if (errOut)
      {
        (*errOut) << "BAG_CHOOSE operator expects a bag, a non-bag is found";
      }
      return TypeNode::null();
    }
  }
  return bagType.getBagElementType();
}

TypeNode BagMapTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}
TypeNode BagMapTypeRule::computeType(NodeManager* nodeManager,
                                     TNode n,
                                     bool check,
                                     std::ostream* errOut)
{
  Assert(n.getKind() == Kind::BAG_MAP);
  TypeNode functionType = n[0].getTypeOrNull();
  TypeNode bagType = n[1].getTypeOrNull();
  if (check)
  {
    if (!bagType.isBag())
    {
      if (errOut)
      {
        (*errOut) << "bag.map operator expects a bag in the second argument, a "
                     "non-bag is found";
      }
      return TypeNode::null();
    }

    TypeNode elementType = bagType.getBagElementType();

    if (!(functionType.isFunction()))
    {
      if (errOut)
      {
        (*errOut) << "Operator " << n.getKind()
                  << " expects a function of type  (-> " << elementType
                  << " *) as a first argument. "
                  << "Found a term of type '" << functionType << "'.";
      }
      return TypeNode::null();
    }
    std::vector<TypeNode> argTypes = functionType.getArgTypes();
    if (!(argTypes.size() == 1 && argTypes[0] == elementType))
    {
      if (errOut)
      {
        (*errOut) << "Operator " << n.getKind()
                  << " expects a function of type  (-> " << elementType
                  << " *). "
                  << "Found a function of type '" << functionType << "'.";
      }
      return TypeNode::null();
    }
  }
  TypeNode rangeType = n[0].getTypeOrNull().getRangeType();
  TypeNode retType = nodeManager->mkBagType(rangeType);
  return retType;
}

TypeNode BagFilterTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}
TypeNode BagFilterTypeRule::computeType(NodeManager* nodeManager,
                                        TNode n,
                                        bool check,
                                        std::ostream* errOut)
{
  Assert(n.getKind() == Kind::BAG_FILTER);
  TypeNode functionType = n[0].getTypeOrNull();
  TypeNode bagType = n[1].getTypeOrNull();
  if (check)
  {
    if (!bagType.isBag())
    {
      if (errOut)
      {
        (*errOut) << "bag.filter operator expects a bag in the second "
                     "argument, a non-bag is found";
      }
      return TypeNode::null();
    }

    TypeNode elementType = bagType.getBagElementType();

    if (!(functionType.isFunction()))
    {
      if (errOut)
      {
        (*errOut) << "Operator " << n.getKind()
                  << " expects a function of type  (-> " << elementType
                  << " Bool) as a first argument. "
                  << "Found a term of type '" << functionType << "'.";
      }
      return TypeNode::null();
    }
    std::vector<TypeNode> argTypes = functionType.getArgTypes();
    if (!(argTypes.size() == 1 && argTypes[0] == elementType
          && functionType.getRangeType() == nodeManager->booleanType()))
    {
      if (errOut)
      {
        (*errOut) << "Operator " << n.getKind()
                  << " expects a function of type  (-> " << elementType
                  << " Bool). "
                  << "Found a function of type '" << functionType << "'.";
      }
      return TypeNode::null();
    }
  }
  return bagType;
}

TypeNode BagAllSomeTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return nm->booleanType();
}

bool checkFunctionTypeFor(const Node& n,
                          const TypeNode& functionType,
                          const TypeNode& bagType,
                          std::ostream* errOut)
{
  // get the element type of the second argument, if it exists
  TypeNode elementType;
  if (bagType.isBag())
  {
    elementType = bagType.getBagElementType();
  }
  if (!functionType.isMaybeKind(Kind::FUNCTION_TYPE))
  {
    if (errOut)
    {
      (*errOut) << "Operator " << n.getKind()
                << " expects a function as a first argument. "
                << "Found a term of type '" << functionType << "'.";
    }
    return false;
  }
  // note that if functionType is abstract, we don't check whether it
  // matches the argument.
  if (functionType.isFunction())
  {
    std::vector<TypeNode> argTypes = functionType.getArgTypes();
    if (!(argTypes.size() == 1
          && (elementType.isNull() || argTypes[0].isComparableTo(elementType))))
    {
      if (errOut)
      {
        (*errOut) << "Operator " << n.getKind()
                  << " expects a function whose type is comparable to the "
                     "type of elements in the set";
        if (!elementType.isNull())
        {
          (*errOut) << " (" << elementType << ")";
        }
        (*errOut) << ". Found a function of type '" << functionType << "'.";
      }
      return false;
    }
  }
  return true;
}

TypeNode BagAllSomeTypeRule::computeType(NodeManager* nodeManager,
                                         TNode n,
                                         bool check,
                                         std::ostream* errOut)
{
  Assert(n.getKind() == Kind::BAG_ALL || n.getKind() == Kind::BAG_SOME);
  std::string op = n.getKind() == Kind::BAG_ALL ? "bag.all" : "bag.some";
  TypeNode functionType = n[0].getTypeOrNull();
  TypeNode bagType = n[1].getTypeOrNull();
  if (check)
  {
    if (!bagType.isMaybeKind(Kind::BAG_TYPE))
    {
      if (errOut)
      {
        (*errOut) << op
                  << " operator expects a bag in the second "
                     "argument, a non-bag is found";
      }
      return TypeNode::null();
    }
    if (!checkFunctionTypeFor(n, functionType, bagType, errOut))
    {
      return TypeNode::null();
    }
    if (functionType.isFunction())
    {
      TypeNode rangeType = functionType.getRangeType();
      if (!rangeType.isBoolean() && !rangeType.isFullyAbstract())
      {
        if (errOut)
        {
          (*errOut) << "Operator " << op
                    << " expects a function returning Bool.";
        }
        return TypeNode::null();
      }
    }
  }
  return nodeManager->booleanType();
}

TypeNode BagFoldTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}
TypeNode BagFoldTypeRule::computeType(NodeManager* nodeManager,
                                      TNode n,
                                      bool check,
                                      std::ostream* errOut)
{
  Assert(n.getKind() == Kind::BAG_FOLD);
  TypeNode functionType = n[0].getTypeOrNull();
  TypeNode initialValueType = n[1].getTypeOrNull();
  TypeNode bagType = n[2].getTypeOrNull();
  if (check)
  {
    if (!bagType.isBag())
    {
      if (errOut)
      {
        (*errOut) << "bag.fold operator expects a bag in the third argument, a "
                     "non-bag is found";
      }
      return TypeNode::null();
    }

    TypeNode elementType = bagType.getBagElementType();

    if (!(functionType.isFunction()))
    {
      if (errOut)
      {
        (*errOut) << "Operator " << n.getKind()
                  << " expects a function of type  (-> " << elementType
                  << " T2 T2) as a first argument. "
                  << "Found a term of type '" << functionType << "'.";
      }
      return TypeNode::null();
    }
    std::vector<TypeNode> argTypes = functionType.getArgTypes();
    TypeNode rangeType = functionType.getRangeType();
    if (!(argTypes.size() == 2 && argTypes[0] == elementType
          && argTypes[1] == rangeType))
    {
      if (errOut)
      {
        (*errOut) << "Operator " << n.getKind()
                  << " expects a function of type  (-> " << elementType
                  << " T2 T2). "
                  << "Found a function of type '" << functionType << "'.";
      }
      return TypeNode::null();
    }
    if (rangeType != initialValueType)
    {
      if (errOut)
      {
        (*errOut) << "Operator " << n.getKind()
                  << " expects an initial value of type " << rangeType
                  << ". Found a term of type '" << initialValueType << "'.";
      }
      return TypeNode::null();
    }
  }
  TypeNode retType = n[0].getTypeOrNull().getRangeType();
  return retType;
}

TypeNode BagPartitionTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}
TypeNode BagPartitionTypeRule::computeType(NodeManager* nodeManager,
                                           TNode n,
                                           bool check,
                                           std::ostream* errOut)
{
  Assert(n.getKind() == Kind::BAG_PARTITION);
  TypeNode functionType = n[0].getTypeOrNull();
  TypeNode bagType = n[1].getTypeOrNull();
  if (check)
  {
    if (!bagType.isBag())
    {
      if (errOut)
      {
        (*errOut) << "bag.partition operator expects a bag in the second "
                     "argument, a non-bag is found";
      }
      return TypeNode::null();
    }

    TypeNode elementType = bagType.getBagElementType();

    if (!(functionType.isFunction()))
    {
      if (errOut)
      {
        (*errOut) << "Operator " << n.getKind()
                  << " expects a function of type  (-> " << elementType << " "
                  << elementType << " Bool) as a first argument. "
                  << "Found a term of type '" << functionType << "'.";
      }
      return TypeNode::null();
    }
    std::vector<TypeNode> argTypes = functionType.getArgTypes();
    TypeNode rangeType = functionType.getRangeType();
    if (!(argTypes.size() == 2 && elementType == argTypes[0]
          && elementType == argTypes[1]
          && rangeType == nodeManager->booleanType()))
    {
      if (errOut)
      {
        (*errOut) << "Operator " << n.getKind()
                  << " expects a function of type  (-> " << elementType << " "
                  << elementType << " Bool) as a first argument. "
                  << "Found a term of type '" << functionType << "'.";
      }
      return TypeNode::null();
    }
  }
  TypeNode retType = nodeManager->mkBagType(bagType);
  return retType;
}

TypeNode TableProductTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}
TypeNode TableProductTypeRule::computeType(NodeManager* nodeManager,
                                           TNode n,
                                           bool check,
                                           std::ostream* errOut)
{
  Assert(n.getKind() == Kind::TABLE_PRODUCT);
  Node A = n[0];
  Node B = n[1];
  TypeNode typeA = n[0].getTypeOrNull();
  TypeNode typeB = n[1].getTypeOrNull();

  if (check && !(typeA.isBag() && typeB.isBag()))
  {
    if (errOut)
    {
      (*errOut) << "Operator " << n.getKind() << " expects two bags. "
                << "Found two terms of types '" << typeA << "' and '" << typeB
                << "' respectively.";
    }
    return TypeNode::null();
  }

  TypeNode elementAType = typeA.getBagElementType();
  TypeNode elementBType = typeB.getBagElementType();

  if (check && !(elementAType.isTuple() && elementBType.isTuple()))
  {
    if (errOut)
    {
      (*errOut) << "Operator " << n.getKind()
                << " expects two tables (bags of tuples). "
                << "Found two terms of types '" << typeA << "' and '" << typeB
                << "' respectively.";
    }
    return TypeNode::null();
  }

  TypeNode retTupleType =
      TupleUtils::concatTupleTypes(elementAType, elementBType);
  TypeNode retType = nodeManager->mkBagType(retTupleType);
  return retType;
}

TypeNode TableProjectTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}
TypeNode TableProjectTypeRule::computeType(NodeManager* nm,
                                           TNode n,
                                           bool check,
                                           std::ostream* errOut)
{
  Assert(n.getKind() == Kind::TABLE_PROJECT && n.hasOperator()
         && n.getOperator().getKind() == Kind::TABLE_PROJECT_OP);
  ProjectOp op = n.getOperator().getConst<ProjectOp>();
  const std::vector<uint32_t>& indices = op.getIndices();
  TypeNode bagType = n[0].getTypeOrNull();
  if (check)
  {
    if (n.getNumChildren() != 1)
    {
      if (errOut)
      {
        (*errOut) << "operands in term " << n << " are " << n.getNumChildren()
                  << ", but TABLE_PROJECT expects 1 operand.";
      }
      return TypeNode::null();
    }

    if (!bagType.isBag())
    {
      if (errOut)
      {
        (*errOut) << "TABLE_PROJECT operator expects a table. Found '" << n[0]
                  << "' of type '" << bagType << "'.";
      }
      return TypeNode::null();
    }

    TypeNode tupleType = bagType.getBagElementType();
    if (!tupleType.isTuple())
    {
      if (errOut)
      {
        (*errOut) << "TABLE_PROJECT operator expects a table. Found '" << n[0]
                  << "' of type '" << bagType << "'.";
      }
      return TypeNode::null();
    }

    // make sure all indices are less than the length of the tuple type
    DType dType = tupleType.getDType();
    DTypeConstructor constructor = dType[0];
    size_t numArgs = constructor.getNumArgs();
    for (uint32_t index : indices)
    {
      if (index >= numArgs)
      {
        if (errOut)
        {
          (*errOut) << "Index " << index << " in term " << n
                    << " is >= " << numArgs
                    << " which is the number of columns in " << n[0] << ".";
        }
        return TypeNode::null();
      }
    }
  }
  TypeNode tupleType = bagType.getBagElementType();
  TypeNode retTupleType =
      TupleUtils::getTupleProjectionType(indices, tupleType);
  return nm->mkBagType(retTupleType);
}

TypeNode TableAggregateTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}
TypeNode TableAggregateTypeRule::computeType(NodeManager* nm,
                                             TNode n,
                                             bool check,
                                             std::ostream* errOut)
{
  Assert(n.getKind() == Kind::TABLE_AGGREGATE && n.hasOperator()
         && n.getOperator().getKind() == Kind::TABLE_AGGREGATE_OP);
  ProjectOp op = n.getOperator().getConst<ProjectOp>();
  const std::vector<uint32_t>& indices = op.getIndices();

  TypeNode functionType = n[0].getTypeOrNull();
  TypeNode initialValueType = n[1].getTypeOrNull();
  TypeNode bagType = n[2].getTypeOrNull();

  if (check)
  {
    if (!bagType.isBag())
    {
      if (errOut)
      {
        (*errOut) << "TABLE_PROJECT operator expects a table. Found '" << n[2]
                  << "' of type '" << bagType << "'.";
      }
      return TypeNode::null();
    }

    TypeNode tupleType = bagType.getBagElementType();
    if (!tupleType.isTuple())
    {
      if (errOut)
      {
        (*errOut) << "TABLE_PROJECT operator expects a table. Found '" << n[2]
                  << "' of type '" << bagType << "'.";
      }
      return TypeNode::null();
    }

    if (!TupleUtils::checkTypeIndices(tupleType, indices))
    {
      if (errOut)
      {
        (*errOut) << "Index in operator of " << n
                  << " is out of range for the type of its argument";
      }
      return TypeNode::null();
    }

    TypeNode elementType = bagType.getBagElementType();

    if (!(functionType.isFunction()))
    {
      if (errOut)
      {
        (*errOut) << "Operator " << n.getKind()
                  << " expects a function of type  (-> " << elementType
                  << " T T) as a first argument. "
                  << "Found a term of type '" << functionType << "'.";
      }
      return TypeNode::null();
    }
    std::vector<TypeNode> argTypes = functionType.getArgTypes();
    TypeNode rangeType = functionType.getRangeType();
    if (!(argTypes.size() == 2 && argTypes[0] == elementType
          && argTypes[1] == rangeType))
    {
      if (errOut)
      {
        (*errOut) << "Operator " << n.getKind()
                  << " expects a function of type  (-> " << elementType
                  << " T T). "
                  << "Found a function of type '" << functionType << "'.";
      }
      return TypeNode::null();
    }
    if (rangeType != initialValueType)
    {
      if (errOut)
      {
        (*errOut) << "Operator " << n.getKind()
                  << " expects an initial value of type " << rangeType
                  << ". Found a term of type '" << initialValueType << "'.";
      }
      return TypeNode::null();
    }
  }
  return nm->mkBagType(functionType.getRangeType());
}

TypeNode TableJoinTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}
TypeNode TableJoinTypeRule::computeType(NodeManager* nm,
                                        TNode n,
                                        bool check,
                                        std::ostream* errOut)
{
  Assert(n.getKind() == Kind::TABLE_JOIN && n.hasOperator()
         && n.getOperator().getKind() == Kind::TABLE_JOIN_OP);
  ProjectOp op = n.getOperator().getConst<ProjectOp>();
  const std::vector<uint32_t>& indices = op.getIndices();
  Node A = n[0];
  Node B = n[1];
  TypeNode aType = A.getTypeOrNull();
  TypeNode bType = B.getTypeOrNull();

  if (check)
  {
    if (!(aType.isBag() && bType.isBag()))
    {
      if (errOut)
      {
        (*errOut) << "TABLE_JOIN operator expects two tables. Found '" << n[0]
                  << "', '" << n[1] << "' of types '" << aType << "', '"
                  << bType << "' respectively. ";
      }
      return TypeNode::null();
    }

    TypeNode aTupleType = aType.getBagElementType();
    TypeNode bTupleType = bType.getBagElementType();
    if (!(aTupleType.isTuple() && bTupleType.isTuple()))
    {
      if (errOut)
      {
        (*errOut) << "TABLE_JOIN operator expects two tables. Found '" << n[0]
                  << "', '" << n[1] << "' of types '" << aType << "', '"
                  << bType << "' respectively. ";
      }
      return TypeNode::null();
    }

    if (indices.size() % 2 != 0)
    {
      if (errOut)
      {
        (*errOut)
            << "TABLE_JOIN operator expects even number of indices. Found "
            << indices.size() << " in term " << n;
      }
      return TypeNode::null();
    }
    auto [aIndices, bIndices] = BagsUtils::splitTableJoinIndices(n);
    if (!TupleUtils::checkTypeIndices(aTupleType, aIndices))
    {
      if (errOut)
      {
        (*errOut) << "Index in operator of " << n
                  << " is out of range for the type of its first argument";
      }
      return TypeNode::null();
    }
    if (!TupleUtils::checkTypeIndices(bTupleType, bIndices))
    {
      if (errOut)
      {
        (*errOut) << "Index in operator of " << n
                  << " is out of range for the type of its second argument";
      }
      return TypeNode::null();
    }

    // check the types of columns
    std::vector<TypeNode> aTypes = aTupleType.getTupleTypes();
    std::vector<TypeNode> bTypes = bTupleType.getTupleTypes();
    for (uint32_t i = 0; i < aIndices.size(); i++)
    {
      if (aTypes[aIndices[i]] != bTypes[bIndices[i]])
      {
        if (errOut)
        {
          (*errOut) << "TABLE_JOIN operator expects column " << aIndices[i]
                    << " in table " << n[0] << " to match column "
                    << bIndices[i] << " in table " << n[1]
                    << ". But their types are " << aTypes[aIndices[i]]
                    << " and " << bTypes[bIndices[i]] << "' respectively. ";
        }
        return TypeNode::null();
      }
    }
  }
  TypeNode aTupleType = aType.getBagElementType();
  TypeNode bTupleType = bType.getBagElementType();
  TypeNode retTupleType = TupleUtils::concatTupleTypes(aTupleType, bTupleType);
  return nm->mkBagType(retTupleType);
}

TypeNode TableGroupTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}
TypeNode TableGroupTypeRule::computeType(NodeManager* nm,
                                         TNode n,
                                         bool check,
                                         std::ostream* errOut)
{
  Assert(n.getKind() == Kind::TABLE_GROUP && n.hasOperator()
         && n.getOperator().getKind() == Kind::TABLE_GROUP_OP);
  ProjectOp op = n.getOperator().getConst<ProjectOp>();
  const std::vector<uint32_t>& indices = op.getIndices();

  TypeNode bagType = n[0].getTypeOrNull();

  if (check)
  {
    if (!bagType.isBag())
    {
      if (errOut)
      {
        (*errOut) << "TABLE_GROUP operator expects a table. Found '" << n[0]
                  << "' of type '" << bagType << "'.";
      }
      return TypeNode::null();
    }

    TypeNode tupleType = bagType.getBagElementType();
    if (!tupleType.isTuple())
    {
      if (errOut)
      {
        (*errOut) << "TABLE_GROUP operator expects a table. Found '" << n[0]
                  << "' of type '" << bagType << "'.";
      }
      return TypeNode::null();
    }

    if (!TupleUtils::checkTypeIndices(tupleType, indices))
    {
      if (errOut)
      {
        (*errOut) << "Index in operator of " << n
                  << " is out of range for the type of its argument";
      }
      return TypeNode::null();
    }
  }
  return nm->mkBagType(bagType);
}

Cardinality BagsProperties::computeCardinality(TypeNode type)
{
  return Cardinality::INTEGERS;
}

bool BagsProperties::isWellFounded(TypeNode type)
{
  return type[0].isWellFounded();
}

Node BagsProperties::mkGroundTerm(TypeNode type)
{
  Assert(type.isBag());
  return type.getNodeManager()->mkConst(EmptyBag(type));
}
}  // namespace bags
}  // namespace theory
}  // namespace cvc5::internal
