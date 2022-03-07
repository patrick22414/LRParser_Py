from collections import deque
from pprint import pprint
from string import ascii_uppercase
from typing import NamedTuple, Optional

from ordered_set import OrderedSet
from typing_extensions import Self


class Token(NamedTuple):
    name: str


class Term(Token):  # Terminals
    def __repr__(self) -> str:
        return "Term(" + self.name + ")"


class NTerm(Token):  # Non-Terminals
    def __repr__(self) -> str:
        return "NTerm(" + self.name + ")"


def make_token(token: str) -> Token:
    if token[0] in ascii_uppercase:
        return NTerm(token)
    elif token[0] == "'":
        return Term(token)
    else:
        raise ValueError


class Rule(NamedTuple):
    left: Token
    right: tuple[Token]

    def __repr__(self) -> str:
        return "Rule: " + str(self.left) + " <= " + " ".join(map(str, self.right))


def make_rule(grammar: str) -> Rule:
    left, right = grammar.split(" <= ")

    left = make_token(left)
    assert isinstance(left, NTerm)

    right = tuple(make_token(token) for token in right.split())

    return Rule(left, right)


class Item(NamedTuple):
    base: Rule
    dot: int

    def move_right(self) -> Self:
        return Item(base=self.base, dot=self.dot + 1)

    def right_of_dot(self) -> Optional[Token]:
        if self.dot < len(self.base.right):
            return self.base.right[self.dot]
        else:
            return None


class ItemSet(tuple[Item]):
    pass


def make_item_set(rule: Rule) -> ItemSet:
    items = (Item(base=rule, dot=dot) for dot in range(len(rule.right) + 1))
    return ItemSet(items)


class State(ItemSet):
    pass


def make_closure(rules: tuple[Rule], items: list[Item]) -> State:
    non_terminals = deque(
        filter(
            lambda token: isinstance(token, NTerm),
            [item.right_of_dot() for item in items],
        )
    )
    seen = set()
    while non_terminals:
        non_term = non_terminals.popleft()
        if non_term not in seen:
            for rule in rules:
                if rule.left == non_term:
                    new_item = Item(base=rule, dot=0)
                    if isinstance(new_item.right_of_dot(), NTerm):
                        non_terminals.append(new_item.right_of_dot())
                    items.append(new_item)
        seen.add(non_term)

    return State(items)


class Action(int):
    pass


class Shift(Action):
    def __str__(self) -> str:
        return "S(" + super().__str__() + ")"


class Reduce(Action):
    def __str__(self) -> str:
        return "R(" + super().__str__() + ")"


class ParsingTable(NamedTuple):
    shift_table: dict[tuple[int, Term], Shift]
    reduce_table: dict[int, Reduce]
    goto_table: dict[tuple[int, NTerm], int]


def make_parsing_table(rules: tuple[Rule]) -> tuple[ParsingTable, OrderedSet[State]]:
    table = ParsingTable(shift_table=dict(), reduce_table=dict(), goto_table=dict())

    state_0 = make_closure(rules, [Item(rules[0], dot=0)])
    queue = deque([state_0])
    states = OrderedSet([state_0])

    while queue:
        src = queue.popleft()
        src_idx = states.index(src)
        print(">>>", src_idx)

        tokens = OrderedSet(item.right_of_dot() for item in src)

        for token in tokens:
            if token is None:
                assert len(src) == 1
                assert all(
                    src_idx != idx for idx, _ in table.shift_table
                ), "Shift-Reduce conflict!"
                assert src_idx not in table.reduce_table, "Reduce-Reduce conflict!"

                table.reduce_table[src_idx] = Reduce(rules.index(src[0].base))
                continue

            item_subset = [
                item.move_right() for item in src if item.right_of_dot() == token
            ]

            dst = make_closure(rules, item_subset)
            if dst not in states:
                queue.append(dst)
                states.add(dst)
            dst_idx = states.index(dst)

            if isinstance(token, Term):
                table.shift_table[(src_idx, token)] = Shift(dst_idx)
            elif isinstance(token, NTerm):
                table.goto_table[(src_idx, token)] = dst_idx
            else:
                raise Exception

    return table, states


def vis_parsing_table(
    rules: tuple[Rule], table: ParsingTable, states: OrderedSet[State]
):
    import pandas as pd

    all_tokens = sorted(set(token for rule in rules for token in rule.right))
    terminals = [token.name for token in all_tokens if isinstance(token, Term)]
    non_terminals = [token.name for token in all_tokens if isinstance(token, NTerm)]

    df = pd.DataFrame(index=range(len(states)), columns=terminals + non_terminals)

    for (r, c), v in table.shift_table.items():
        df.at[r, c.name] = str(v)
    for r, v in table.reduce_table.items():
        df.iloc[r, 0 : len(terminals)] = str(v)
    for (r, c), v in table.goto_table.items():
        df.at[r, c.name] = v

    print(df)


if __name__ == "__main__":
    rules = [
        "START <= Expr '$'",
        "Expr <= Expr '*' Atom",
        "Expr <= Expr '+' Atom",
        "Expr <= Atom",
        "Atom <= '0'",
        "Atom <= '1'",
    ]
    rules = [make_rule(r) for r in rules]

    pprint(rules)

    items = make_item_set(rules[0])
    pprint(items)

    table, states = make_parsing_table(rules)
    pprint(table)
    for state in states:
        pprint(state)

    vis_parsing_table(rules, table, states)
