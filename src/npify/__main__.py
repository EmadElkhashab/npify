from dataclasses import dataclass
from itertools import chain
from io import StringIO
from typing import List, Type

from timeit import timeit


def bool_var(cls):
    cls = dataclass(frozen=True, slots=True)(cls)
    return cls


class BooleanVariable:
    def __invert__(self):
        return BooleanLiteral(self, negated=True)

    def to_int(self, varDict):
        return varDict[self]


@dataclass(slots=True)
class BooleanLiteral:
    variable: BooleanVariable
    negated: bool = False

    def __str__(self):
        if self.negated:
            return f"~{self.variable}"
        else:
            return str(self.variable)

    def __invert__(self):
        return BooleanLiteral(self.variable, negated=not self.negated)

    def to_int(self, varDict):
        if self.negated:
            return -varDict[self.variable]
        else:
            return varDict[self.variable]


@bool_var
class Match(BooleanVariable):
    pigeon: int
    hole: int

    def __str__(self):
        return f"x{self.pigeon, self.hole}"


class VarDict(dict):
    def __init__(self):
        self.num_vars = 0

    def __missing__(self, key) -> int:
        self.num_vars += 1
        return self.num_vars


class CNFPrinter:
    def __init__(self, file):
        self.file = file
        self.vars = VarDict()

    def or_iter(self, iterator) -> None:
        print(" ".join(str(x.to_int(self.vars)) for x in iterator), file=self.file)

    def or_(self, *args) -> None:
        print(" ".join(str(x.to_int(self.vars)) for x in args), file=self.file)


def php_nice(n) -> str:
    npigeons = n
    nholes = n
    pigeons = list(range(npigeons))
    holes = list(range(nholes))

    buffer = StringIO()
    encoder = CNFPrinter(buffer)

    for p in pigeons:
        encoder.or_iter(Match(p, h) for h in holes)

    for h in holes:
        for p1 in pigeons:
            for p2 in pigeons:
                if p1 != p2:
                    encoder.or_(~Match(p1, h), ~Match(p2, h))

    return buffer.getvalue()


def php_raw(n):
    npigeons = n
    nholes = n
    pigeons = list(range(npigeons))
    holes = list(range(nholes))

    variables = VarDict()

    buffer = StringIO()

    for p in pigeons:
        print(*(variables[p, h] for h in holes), file=buffer)

    for h in holes:
        for p1 in pigeons:
            for p2 in pigeons:
                if p1 != p2:
                    print(-variables[p1, h], -variables[p2, h], file=buffer)

    return buffer.getvalue()


class Expression:
    def fol_string(self) -> str:
        raise NotImplementedError

    def cnf(self) -> List[List[BooleanVariable | BooleanLiteral]]:
        raise NotImplementedError


class RootNode:
    expression: Expression = None

    def fol_string(self) -> str:
        return self.expression.fol_string()

    def cnf(self) -> List[List[BooleanVariable | BooleanLiteral]]:
        return self.expression.cnf()


@dataclass
class VariableNode(Expression):
    name: str

    def fol_string(self) -> str:
        return self.name

    def cnf(self, **vars: int) -> List[List[BooleanVariable | BooleanLiteral]]:
        return [[BooleanVariable()]]


@dataclass
class ConditionNode(Expression):
    def is_true(self) -> bool:
        raise NotImplementedError


@dataclass
class EqualityNode(ConditionNode):
    left: VariableNode
    right: VariableNode

    def fol_string(self) -> str:
        return f"{self.left.name} = {self.right.name}"

    def is_true(self, **vars: int) -> bool:
        return vars[self.left.name] == vars[self.right.name]


@dataclass
class InequalityNode(ConditionNode):
    left: VariableNode
    right: VariableNode

    def fol_string(self) -> str:
        return f"{self.left.name} ≠ {self.right.name}"

    def is_true(self, **vars: int) -> bool:
        return vars[self.left.name] != vars[self.right.name]


@dataclass
class QuantifierNode(Expression):
    variable: VariableNode
    iterable: List[int]
    expression: Expression
    conditions: List[ConditionNode]

    def fol_string(self) -> str:
        return (
            f"{self.variable.name} ∈ {self.iterable}"
            + (
                f", {', '.join(x.fol_string() for x in self.conditions)}"
                if self.conditions
                else ""
            )
            + f" : {self.expression.fol_string()}"
        )


class ForAllNode(QuantifierNode):
    def fol_string(self) -> str:
        return f"∀ {super().fol_string()}"

    def cnf(self, **vars: int) -> List[List[BooleanVariable | BooleanLiteral]]:
        return list(
            chain.from_iterable(
                self.expression.cnf(**{self.variable.name: value}, **vars)
                for value in self.iterable
                if all(
                    cond.is_true(**{self.variable.name: value}, **vars)
                    for cond in self.conditions or []
                )
            )
        )


class ExistsNode(QuantifierNode):
    def fol_string(self) -> str:
        return f"∃ {super().fol_string()}"

    def cnf(self, **vars: int) -> List[List[BooleanVariable | BooleanLiteral]]:
        return [
            list(
                chain.from_iterable(
                    chain(*self.expression.cnf(**{self.variable.name: value}, **vars))
                    for value in self.iterable
                    if all(
                        cond.is_true(**{self.variable.name: value}, **vars)
                        for cond in self.conditions or []
                    )
                )
            )
        ]


@dataclass
class OrNode(Expression):
    args: List[Expression]

    def fol_string(self) -> str:
        return " ∨ ".join(arg.fol_string() for arg in self.args)

    def cnf(self, **vars: int) -> List[List[BooleanVariable | BooleanLiteral]]:
        return [
            list(chain.from_iterable(chain(*(arg.cnf(**vars))) for arg in self.args))
        ]


@dataclass
class AndNode(Expression):
    args: List[Expression]

    def fol_string(self) -> str:
        return " ∧ ".join(arg.fol_string() for arg in self.args)

    def cnf(self, **vars: int) -> List[List[BooleanVariable | BooleanLiteral]]:
        return list(chain.from_iterable((arg.cnf(**vars)) for arg in self.args))


@dataclass
class NotNode(Expression):
    expression: Expression

    def fol_string(self) -> str:
        return f"¬ {self.expression.fol_string()}"

    def cnf(self, **vars: int) -> List[List[BooleanVariable | BooleanLiteral]]:
        return [[~x for x in chain(*self.expression.cnf(**vars))]]


@dataclass
class PredicateNode(Expression):
    constructor: Type
    args: List[VariableNode]

    def fol_string(self) -> str:
        return f"{self.constructor.__name__}({', '.join(arg.fol_string() for arg in self.args)})"

    def cnf(self, **vars: int) -> List[List[BooleanVariable | BooleanLiteral]]:
        return [[self.constructor(*tuple(vars[arg.name] for arg in self.args))]]


class Builder:
    """Build an abstract syntax tree that can later be evaluated."""

    def __init__(self):
        self.root = RootNode()
        self.current_node = self.root

    def forall(self, **kwargs):
        for key, value in kwargs.items():
            self.current_node.expression = ForAllNode(
                VariableNode(name=key), value, None, None
            )
            self.current_node = self.current_node.expression

        return self

    def exists(self, **kwargs):
        for key, value in kwargs.items():
            self.current_node.expression = ExistsNode(
                VariableNode(name=key), value, None, None
            )
            self.current_node = self.current_node.expression

        return self

    def if_(self, *conditions: ConditionNode):
        if self.current_node.conditions is None:
            self.current_node.conditions = conditions
        else:
            self.current_node.conditions.extend(conditions)

        return self

    def or_(self, *args: Expression):
        self.current_node.expression = OrNode(args)

        return self

    def and_(self, *args: Expression):
        self.current_node.expression = AndNode(args)

        return self

    def end(self) -> Expression:
        expression = self.root.expression
        self.root.expression = None
        self.current_node = self.root
        return expression

    def fol_string(self, expression: Expression = None):
        if expression is None:
            expression = self.root.expression

        return expression.fol_string()
    
    def cnf(self, expression: Expression = None):
        if expression is None:
            expression = self.root.expression

        return expression.cnf()

def test_case():
    b = Builder()
    o1 = (
        b.forall(p=[1, 2])
        .exists(h=[1])
        .or_(PredicateNode(Match, [VariableNode("p"), VariableNode("h")]))
        .end()
    )
    print(o1.fol_string())
    # print(o1.cnf())
    o2 = (
        b.forall(p1=[1, 2])
        .forall(p2=[1, 2])
        .forall(h=[1])
        .if_(InequalityNode(VariableNode("p1"), VariableNode("p2")))
        .or_(
            NotNode(PredicateNode(Match, [VariableNode("p1"), VariableNode("h")])),
            NotNode(PredicateNode(Match, [VariableNode("p2"), VariableNode("h")])),
        )
        .end()
    )
    print(o2.fol_string())
    # print(o2.cnf())
    o = b.and_(o1, o2).end()
    print(o.fol_string())
    # print(o.cnf())

    # buffer = StringIO()
    # encoder = CNFPrinter(buffer)

    # for clause in o.cnf():
        # encoder.or_iter(clause)

    # print(buffer.getvalue())



def generate(ast: Builder, file: StringIO):
    """Evaluate the given abstract syntax tree and write the result to the given file."""
    encoder = CNFPrinter(file)

    for clause in ast.cnf():
        encoder.or_iter(clause)

def php_builder(n):
    builder = Builder()

    pigeons = list(range(n))
    holes = list(range(n))

    one_hole_per_pigeon = (
        builder.forall(p=pigeons)
        .exists(h=holes)
        .or_(PredicateNode(Match, [VariableNode("p"), VariableNode("h")]))
        .end()
    )
    one_pigeon_per_hole = (
        builder.forall(h=holes)
        .forall(p1=pigeons)
        .forall(p2=pigeons)
        .if_(InequalityNode(VariableNode("p1"), VariableNode("p2")))
        .or_(
            NotNode(PredicateNode(Match, [VariableNode("p1"), VariableNode("h")])),
            NotNode(PredicateNode(Match, [VariableNode("p2"), VariableNode("h")])),
        )
        .end()
    )

    buffer = StringIO()
    generate(builder.and_(one_hole_per_pigeon, one_pigeon_per_hole), buffer)
    return buffer.getvalue()

    # builder.forall(p=pigeons).at_least_one(var('Match(p,h)').for_(h=holes))


def main():
    print("nice", timeit("php_nice(40)", number=10, globals=globals()))
    print("raw", timeit("php_raw(40)", number=10, globals=globals()))
    print("builder", timeit("php_builder(40)", number=10, globals=globals()))

    a = php_nice(40)
    b = php_raw(40)
    c = php_builder(40)

    assert a == b
    assert b == c


if __name__ == "__main__":
    test_case()
    main()