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

package tools.aqua.wvm.machine

import tools.aqua.wvm.analysis.hoare.SMTSolver
import tools.aqua.wvm.analysis.hoare.WPCProofSystem
import java.math.BigInteger
import java.util.Scanner
import tools.aqua.wvm.analysis.semantics.StatementApp
import tools.aqua.wvm.language.*

data class Context(
    val scope: Scope,
    val program: List<Statement>,
    val pre: BooleanExpression = True,
    val post: BooleanExpression = True,
    var input: Scanner? = null,
    var model: Map<String, String>?=null
) {
  fun execute(verbose: Boolean, output: Output = Output(), maxSteps: Int = -1): List<StatementApp> {
    var cfg = Configuration(SequenceOfStatements(program), scope, initMemForScope())
    var trace = listOf<StatementApp>()
    var stepCount = 0
    if (verbose) println(cfg)
    while (!cfg.isFinal()) {
      stepCount++
      if (maxSteps in 1 ..< stepCount) {
        output.println("Terminated after ${maxSteps} steps.")
        break
      }
      val step = cfg.statements.head().execute(cfg, input)
      if (step.result.output != null) {
        output.println(step.result.output)
      }
      trace = trace + step
      cfg = step.result.dst
      if (verbose) println(cfg)
    }
    if (cfg.error) {
      output.println("Terminated abnormally.")
    }
    if (verbose) println("end.")
    return trace
  }
  fun augment(scope: Scope): BooleanExpression? {
    var newPre: BooleanExpression? = null

    // Process all symbols (both variables and array elements)
    scope.symbols.forEach { entry ->
      val variableName = entry.key
      val variableValue = entry.value.first

      if (entry.value.size == 1) {
        val varData = variableValue.split("..")
        if (varData.size == 2) {
          val eq1 = Gte(
            ValAtAddr(Variable(variableName)),
            NumericLiteral(varData[0].replace("\\s".toRegex(), "").toBigInteger())
          )
          val eq2 = Lte(
            ValAtAddr(Variable(variableName)),
            NumericLiteral(varData[1].replace("\\s".toRegex(), "").toBigInteger())
          )
          newPre = if (newPre == null) And(eq1, eq2) else And(newPre!!, And(eq1, eq2))
        } else {
          val expectedValue = NumericLiteral(variableValue.toBigInteger())
          val eq = Eq(ValAtAddr(Variable(variableName)), expectedValue, 0)
          newPre = if (newPre == null) eq else And(newPre!!, eq)
        }
      } else {
        val arrayValues = variableValue.split(",")
        var i = 0
        for (value in arrayValues) {
          val varData = value.split("..")
          if (varData.size == 2) {
            val eq1 = Gte(
              ValAtAddr(Variable("$variableName$i")),
              NumericLiteral(varData[0].toBigInteger())
            )
            val eq2 = Lte(
              ValAtAddr(Variable("$variableName$i")),
              NumericLiteral(varData[1].toBigInteger())
            )
            newPre = if (newPre == null) And(eq1, eq2) else And(newPre!!, And(eq1, eq2))
          } else {
            val expectedValue = NumericLiteral(value.toBigInteger())
            val eq = Eq(ValAtAddr(Variable(variableName)), expectedValue, 0)
            newPre = if (newPre == null) eq else And(newPre!!, eq)
          }
          i++
        }
      }
    }

    return newPre
  }
  private fun initMemForScope(): Memory {
    val declarationBlock = augment(this.scope)
    val expr = And(this.pre,declarationBlock!!)
    val smtSolver = SMTSolver()
    val model = smtSolver.solve(expr).model
    this.model=model
    if (1!=1) {
      var memArray = Array(scope.size) { BigInteger.ZERO }
      val keysList = scope.symbols.keys.toList().map { key ->
        if (key.matches(Regex("([a-zA-Z_][a-zA-Z_0-9]*)\\[(\\d+)]"))) {
          val matchResult = Regex("([a-zA-Z_][a-zA-Z_0-9]*)\\[(\\d+)]").find(key)
          val (arrayName, index) = matchResult!!.destructured
          "array_${arrayName}${index}" // Transform to array_y0 format
        } else {
          key // Leave unchanged if it doesn't match the pattern
        }
      }

      var i = 0
      if(model.size!=0) {
        while (i < memArray.size) {
          memArray[i] = model.get(keysList.get(i))!!.toBigInteger()
          i = i + 1
        }

      }
      else{
        throw Exception("Solution not possible !")
      }
      var mem = Memory(memArray)

      return mem
    } else {
      val keysList = scope.symbols.keys.toList()
      val input_Array= this.input!!.nextLine().split(" ")
      var memArray = Array(scope.size) { BigInteger.ZERO }
      var i = 0
      var j = 0
      while (i < memArray.size) {
        val ArrayValues = scope.symbols.get(keysList.get(i))!!.first
        if(ArrayValues.split("..").size==2){
          if (j<input_Array.size){
            if(scope.symbols.get(keysList.get(i))!!.input!!.inRange(input_Array.get(j).toInt())) {
              scope.symbols.get(keysList.get(i))!!.UserInput= input_Array.get(j).toBigInteger().toString()
              memArray[i] = input_Array.get(j).toBigInteger()
              j++
            }
            else{
              throw IllegalArgumentException("Error : Input not in range")
            }
          }
          else{
            throw IllegalArgumentException("Error : Not enough inputs")
          }
        }
        else {
          scope.symbols.get(keysList.get(i))!!.UserInput= scope.symbols.get(keysList.get(i))!!.first.toBigInteger().toString()
          memArray[i] = scope.symbols.get(keysList.get(i))!!.first.toBigInteger()
        }
        i = i + 1
      }
      var mem = Memory(memArray)
      return mem
    }
  }

  override fun toString(): String {
    return "$scope\n $program"
  }
}
