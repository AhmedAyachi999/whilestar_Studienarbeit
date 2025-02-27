/*
 * SPDX-License-Identifier: Apache-2.0
 *
 * Copyright 2024-2024 The While* Authors
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package tools.aqua.wvm.analysis.hoare

import tools.aqua.konstraints.parser.Context
import tools.aqua.konstraints.parser.SortedVar
import tools.aqua.konstraints.smt.*
import tools.aqua.konstraints.smt.Expression
import tools.aqua.konstraints.theories.*
import tools.aqua.wvm.language.*
import tools.aqua.wvm.language.And
import tools.aqua.wvm.language.False
import tools.aqua.wvm.language.Not
import tools.aqua.wvm.language.Or
import tools.aqua.wvm.language.True

class SMTSolver {

  class Result(val status: SatStatus, val model: Map<String, String>)

  var vars = mapOf<String, DeclareConst>()

  val ctx = Context(QF_LIA)

  fun asKonstraint(expr: AddressExpression): Expression<IntSort> {
    var exprString = expr.toString()
    // Because of the SMTsolver.solve() method, we cannot use a[0], we transform it instead to array_a0
    if(exprString.contains("[")){
      exprString = "array_"+exprString.replace(Regex("[\\[\\]]"), "")
    }
    if (expr is Variable || expr is ArrayAccess ) {
      if (!vars.containsKey(exprString)) {
        vars += (exprString to DeclareConst(Symbol(exprString), IntSort))
      }
      return UserDeclaredExpression(Symbol(exprString), IntSort)
    } else throw Exception("WPC Proof System cannot compute with address expression ${expr}")
  }

  fun asKonstraint(expr: ArithmeticExpression): Expression<IntSort> =
      when (expr) {
        is NumericLiteral -> IntLiteral(expr.literal)
        is Add -> IntAdd(listOf(asKonstraint(expr.left), asKonstraint(expr.right)))
        is Div -> IntDiv(listOf(asKonstraint(expr.left), asKonstraint(expr.right)))
        is Mul -> IntMul(listOf(asKonstraint(expr.left), asKonstraint(expr.right)))
        is Rem -> throw Exception("WPC Proof System cannot compute with remainder ${expr}")
        is Sub -> IntSub(listOf(asKonstraint(expr.left), asKonstraint(expr.right)))
        is UnaryMinus -> IntNeg(asKonstraint(expr.negated))
        is ValAtAddr -> asKonstraint(expr.addr)
        is VarAddress -> throw Exception("WPC Proof System cannot compute with var address ${expr}")
      }

  fun asKonstraint(expr: BooleanExpression): Expression<BoolSort> =
      when (expr) {
        is True -> tools.aqua.konstraints.theories.True
        is False -> tools.aqua.konstraints.theories.False
        is And ->
            tools.aqua.konstraints.theories.And(asKonstraint(expr.left), asKonstraint(expr.right))
        is Or ->
            tools.aqua.konstraints.theories.Or(asKonstraint(expr.left), asKonstraint(expr.right))
        is Imply -> Implies(asKonstraint(expr.left), asKonstraint(expr.right))
        is Equiv -> Equals(asKonstraint(expr.left), asKonstraint(expr.right))
        is Not -> tools.aqua.konstraints.theories.Not(asKonstraint(expr.negated))
        is Gt -> IntGreater(asKonstraint(expr.left), asKonstraint(expr.right))
        is Gte -> IntGreaterEq(asKonstraint(expr.left), asKonstraint(expr.right))
        is Lt -> IntLess(asKonstraint(expr.left), asKonstraint(expr.right))
        is Lte -> IntLessEq(asKonstraint(expr.left), asKonstraint(expr.right))
        is Eq -> Equals(asKonstraint(expr.left), asKonstraint(expr.right))
        is Forall ->
            ForallExpression(
                listOf(SortedVar(Symbol(expr.boundVar.name), IntSort)),
                asKonstraint(expr.expression))
      }

  fun solve(expr: BooleanExpression): Result {
    val konstraint = asKonstraint(expr)
    var commands = vars.values + Assert(konstraint) + CheckSat
    val smtProgram = DefaultSMTProgram(commands, ctx)
    var model = emptyMap<String, String>()
    smtProgram.solve()
    if (smtProgram.status == SatStatus.SAT) {
      commands += GetModel
      val progForModel = DefaultSMTProgram(commands, ctx)
      progForModel.solve()
      model =
          progForModel.model?.definitions?.associate { it ->
            (it.name.toString() to it.term.toString())
          } ?: emptyMap()
    }
    return Result(smtProgram.status, model)
  }
}
