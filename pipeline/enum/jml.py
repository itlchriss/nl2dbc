from enum import Enum


class JML(Enum):
    Requires = 1
    Ensures = 2
    Signals = 3
    Invariant = 4
    Assignable = 5
    Nonnullelements = 6
    Result = 7
    Old = 8
    Forall = 9
    Exists = 10
    Also = 11
    Nothing = 12

    @classmethod
    def toString(cls, val):
        if val == JML.Requires: return 'requires'
        if val == JML.Ensures: return 'ensures'
        if val == JML.Signals: return 'signals'
        if val == JML.Invariant: return 'invariant'
        if val == JML.Assignable: return 'assignable'
        if val == JML.Nonnullelements: return 'nonnullelements'
        if val == JML.Result: return r"\result"
        if val == JML.Old: return r"\old"
        if val == JML.Forall: return r"\forall"
        if val == JML.Exists: return r"\exists"
        if val == JML.Nothing: return r'\nothing'

    def __str__(self):
        if self is JML.Requires: return 'requires'
        if self is JML.Ensures: return 'ensures'
        if self is JML.Signals: return 'signals'
        if self is JML.Invariant: return 'invariant'
        if self is JML.Assignable: return 'assignable'
        if self is JML.Nonnullelements: return 'nonnullelements'
        if self is JML.Result: return r"\result"
        if self is JML.Old: return r"\old"
        if self is JML.Forall: return r"\forall"
        if self is JML.Exists: return r"\exists"
        if self is JML.Nothing: return r'\nothing'
