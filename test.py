from nltk import Prover9, Variable
from nltk.sem import Expression
from nltk.sem.logic import LambdaExpression

read_expr = Expression.fromstring
# p1 = read_expr(r'\P y x.(P(x, y))')
# p2 = read_expr(r'\x.ascending(x)')
# p3 = read_expr(r'order')
# p_sort = read_expr(r'\P x.(sort(F, x, P(x)))')
# p4 = p1(p2).simplify()
# print(p4)
# p5 = p4(p3).simplify()
# print(p5)
# p6 = p_sort(p5).simplify()
# print(p6)
# pr = read_expr(r'exists x.(result(x) & (\x.input_array(x) & \x.sort(x,ascend(order)))(x) & all y.(result(y) <-> (y = x)))')
# print(pr.simplify())
p = read_expr(r'\P Q x.(P(x) & Q(x))')
p1 = read_expr(r'\x.input_array(x, ascend(order))')
print(p(p1).simplify())

# import spacy
# from spacy import displacy
# from collections import Counter
#
# nlp = spacy.load('en_core_web_lg')
# doc = nlp('the result should be the input array sorted in ascending order.')
# print([(X.text, X.label_) for X in doc.ents])
