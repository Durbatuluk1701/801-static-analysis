# imp_ast.py
# ----------
# This file defines the data structures we will be the output of our
# parser. We will write our parser using our combinator library which
# will convert the list of tokens returned by the lexer into an AST.
# Once the AST is finished, we can easily execute the program.
#
# There are three kinds of structures in IMP:
#   1. Arithmetic expressions, used to compute numbers.
#   2. Boolean expressions, used to compute conditions for if/while statements.
#   3. Statements
#
# Starting with arithmetic expressions, these can take the following forms:
#   * Literal integer constants, such as 42
#   * Variables such as x, y
#   * Binary operations, such as x + 42, constructed from other arithmetic
#     expressions.
#
# We can group expressions together with parenthesis, such as (x + 2) * 3.
# The above isn't a different kind of expression, just a different way to
# parser the expression.
#
# Implementation:
#   * We will define three classes for the three different expression forms,
#     plus a base class for arithmetic expressions in general. For now, the
#     classes won't do much except contain data.
#   * Include a __repr__ method for printing out the AST for debugging purposes.
#   * All AST classes will subclass `Equality` so we can check if two AST objects
#     are the same, to help with testing.

from IMP.equality import Equality


class Statement(Equality):
    pass


class Aexp(Equality):
    pass


# Boolean expressions are the next on our list. There are four kinds of
# Boolean expressions.
#
# * Relational expressions (ex: x < 20)
# * AND expressions (such as x < 20 and y > 20)
# * OR expressions
# * NOT expressions
#
# The left and right sides of a relational expressions are arithmetic expressions.
# The left and right sides of any "AND", "OR" or "NOT" expression are Boolean
# expressions. Restricting the type like this will help us avoid expressions such as:
#
#                                   X < 10 and 30
class Bexp(Equality):
    pass


# Next we focus on statements, which can contain both arithmetic and boolean expressions.
# There are four kinds of statements: assignment, compound, conditional and loops.
class Assignment(Statement):
    def __init__(self, name, aexp):
        self.name = name
        self.aexp = aexp

    def to_str(self, tabNum):
        tabs = "\t" * tabNum
        tabs_plus = "\t" * (tabNum + 1)
        return (
            tabs
            + "Assignment(\n%s, \n%s\n"
            % (
                tabs_plus + self.name.to_str(tabNum + 1),
                tabs_plus + self.aexp.to_str(tabNum + 1),
            )
            + tabs
            + ")"
        )

    def eval(self, env):
        value = self.aexp.eval(env)
        env[self.name] = value


class Sequence(Statement):
    def __init__(self, first, second):
        self.first = first
        self.second = second

    def to_str(self, tabNum):
        tabs = "\t" * tabNum
        tabs_plus = "\t" * (tabNum + 1)
        return (
            tabs
            + "Sequence(\n%s, \n%s\n"
            % (
                tabs_plus + self.first.to_str(tabNum + 1),
                tabs_plus + self.second.tost_str(tabNum + 1),
            )
            + tabs
            + ")"
        )

    def eval(self, env):
        self.first.eval(env)
        self.second.eval(env)


class Ite(Statement):
    def __init__(self, condition, true_stmt, false_stmt):
        self.condition = condition
        self.true_stmt = true_stmt
        self.false_stmt = false_stmt

    def to_str(self, tabNum):
        tabs = "\t" * tabNum
        tabs_plus = "\t" * (tabNum + 1)
        return (
            tabs
            + "Ite(\n%s, \n%s, \n%s\n"
            % (
                tabs_plus + self.condition.to_str(tabNum + 1),
                tabs_plus + self.true_stmt.to_str(tabNum + 1),
                tabs_plus + self.false_stmt.to_str(tabNum + 1),
            )
            + tabs
            + ")"
        )

    def eval(self, env):
        condition_value = self.condition.eval(env)
        if condition_value:
            self.true_stmt.eval(env)
        else:
            if self.false_stmt:
                self.false_stmt.eval(env)


class While(Statement):
    def __init__(self, condition, body):
        self.condition = condition
        self.body = body

    def to_str(self, tabNum):
        tabs = "\t" * tabNum
        tabs_plus = "\t" * (tabNum + 1)
        return (
            tabs
            + "While(\n%s, \n%s\n"
            % (
                tabs_plus + self.condition.to_str(tabNum + 1),
                tabs_plus + self.body.to_str(tabNum + 1),
            )
            + tabs
            + ")"
        )

    def eval(self, env):
        condition_value = self.condition.eval(env)
        while condition_value:
            self.body.eval(env)
            condition_value = self.condition.eval(env)


class Skip:
    def __init__(self):
        pass

    def to_str(self, tabNum):
        tabs = "\t" * tabNum
        return tabs + "Skip"

    def eval(self, env):
        pass


class IntAexp(Aexp):
    def __init__(self, i):
        self.i = i

    def to_str(self, tabNum):
        tabs = "\t" * tabNum
        tabs_plus = "\t" * (tabNum + 1)
        return (
            tabs
            + "IntAexp(\n%d\n" % (tabs_plus + self.i.to_str(tabNum + 1))
            + tabs
            + ")"
        )

    def eval(self, env):
        return self.i


class VarAexp(Aexp):
    def __init__(self, name):
        self.name = name

    def to_str(self, tabNum):
        tabs = "\t" * tabNum
        tabs_plus = "\t" * (tabNum + 1)
        return (
            tabs
            + "VarAexp(\n%s" % (tabs_plus + self.name.toStr(tabNum + 1))
            + tabs
            + ")"
        )

    def eval(self, env):
        if self.name in env:
            return env[self.name]
        else:
            return 0


class BinopAexp(Aexp):
    def __init__(self, op, left, right):
        self.op = op
        self.left = left
        self.right = right

    def to_str(self, tabNum):
        tabs = "\t" * tabNum
        tabs_plus = "\t" * (tabNum + 1)
        return (
            tabs
            + "BinopAexp(\n%s, \n%s, \n%s\n"
            % (
                tabs_plus + self.op.to_str(tabNum + 1),
                tabs_plus + self.left.to_str(tabNum + 1),
                tabs_plus + self.right.to_str(tabNum + 1),
            )
            + tabs
            + ")"
        )

    def eval(self, env):
        left_value = self.left.eval(env)
        right_value = self.right.eval(env)
        if self.op == "+":
            value = left_value + right_value
        elif self.op == "-":
            value = left_value - right_value
        elif self.op == "*":
            value = left_value * right_value
        elif self.op == "/":
            value = left_value / right_value
        else:
            raise RuntimeError("unknown operator: " + self.op)
        return value


class RelopBexp(Bexp):
    def __init__(self, op, left, right):
        self.op = op
        self.left = left
        self.right = right

    def to_str(self, tabNum):
        tabs = "\t" * tabNum
        tabs_plus = "\t" * (tabNum + 1)
        return (
            "RelopBexp(\n%s, \n%s, \n%s\n"
            % (
                tabs_plus + self.op.to_str(tabNum + 1),
                tabs_plus + self.left.to_str(tabNum + 1),
                tabs_plus + self.right.to_str(tabNum + 1),
            )
            + tabs
            + ")"
        )

    def eval(self, env):
        left_value = self.left.eval(env)
        right_value = self.right.eval(env)
        if self.op == "<":
            value = left_value < right_value
        elif self.op == "<=":
            value = left_value <= right_value
        elif self.op == ">":
            value = left_value > right_value
        elif self.op == ">=":
            value = left_value >= right_value
        elif self.op == "=":
            value = left_value == right_value
        elif self.op == "!=":
            value = left_value != right_value
        else:
            raise RuntimeError("unknown operator: " + self.op)
        return value


class AndBexp(Bexp):
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def to_str(self, tabNum):
        tabs = "\t" * tabNum
        tabs_plus = "\t" * (tabNum + 1)
        return (
            tabs
            + "AndBexp(\n%s, \n%s\n"
            % (
                tabs_plus + self.left.to_str(tabNum + 1),
                tabs_plus + self.right.to_str(tabNum + 1),
            )
            + tabs
            + ")"
        )

    def eval(self, env):
        left_value = self.left.eval(env)
        right_value = self.right.eval(env)
        return left_value and right_value


class OrBexp(Bexp):
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def to_str(self, tabNum):
        tabs = "\t" * tabNum
        tabs_plus = "\t" * (tabNum + 1)
        return (
            tabs
            + "OrBexp(\n%s, \n%s\n"
            % (
                tabs_plus + self.left.to_str(tabNum + 1),
                tabs_plus + self.right.to_str(tabNum + 1),
            )
            + tabs
            + ")"
        )

    def eval(self, env):
        left_value = self.left.eval(env)
        right_value = self.right.eval(env)
        return left_value or right_value


class NotBexp(Bexp):
    def __init__(self, exp):
        self.exp = exp

    def to_str(self, tabNum):
        tabs = "\t" * tabNum
        tabs_plus = "\t" * (tabNum + 1)
        return (
            tabs + "NotBexp(\n%s\n" % (tabs_plus + self.exp.to_str(tabNum)) + tabs + ")"
        )

    def eval(self, env):
        value = self.exp.eval(env)
        return not value
