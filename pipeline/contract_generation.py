from typing import List, Tuple
import re



import nltk
from nltk import parse
from nltk.featstruct import FeatureValueTuple

from pipeline.enum.contract_types import SpecTypes
from pipeline.enum.jml import JML


class ContractGeneration:
    __grammar = None
    __enable_trace = 0
    __failed_CFG_parsing_count = 0
    __failed_CNL_collection_count = 0

    __leading_operators = "!<>"
    __following_operators = "="

    # __java_operators = ["++", "--", "+", "-", "~", ""]

    # predefining a set of word classes that we want to ignore their values
    __useless_word_classes = ['DT']

    # predefining a set of characters that we cannot process
    # return is not useless, but we have further usage
    __useless_chars = ['-LRB-', '-RRB-', '-LSB-', '-RSB-']

    # predefined words
    __predefined_feature_lexicons = [
        ('less', 'JJ'), ('great', 'JJ'),
        ('than', 'IN'),
        ('be', 'VB'), ('contain', 'VB'),
        ('argument', 'NN'), ('parameter', 'NN'), ('alphabet', 'NN'),
        # ('return', 'VB'), ('be', 'VB'), ('Return', 'VB'),
        ('not', 'RB'), ('only', 'RB'),
        ('the', 'DT'), ('this', 'DT'),
        ('and', 'CC')
        # ('should', 'MD'),
        # ('.', '.'),
        # (',', ','), (';', ';'), (';', ':'), (':', '-'), ('-', ':')
        # TODO: comma should be considered as conjunction. skip it currently for easy parsing
    ]

    def __init__(self, grammar, enable_trace=0):
        self.__grammar = grammar
        self.__enable_trace = enable_trace

    # def generate(self, normalised_data: Tuple[List[str], List[Tuple]],
    #              spec_type: SpecTypes, param_name: str = None) -> List[str]:
    def generate(self, tags: List[Tuple],
                     spec_type: SpecTypes, param_name: str = None) -> List[str]:
        # tokens = normalised_data[0]
        # tags = normalised_data[1]
        tokens = [t[0] for t in tags]
        contracts = []

        lex = self.__lexical_production(tags)
        lex_prod = '\n'.join([line for line in lex])
        print(lex_prod)
        grammar = nltk.grammar.FeatureGrammar.fromstring(self.__grammar + '\n' + lex_prod)
        print(grammar)
        parser = parse.FeatureEarleyChartParser(grammar, trace=self.__enable_trace)
        try:
            parses = parser.parse(tokens)
            # GLR like approach: we are translating all the parsing trees
            # TODO: we need to have syntax checking and scoring methodology for the contracts
            tree_count = 0
            while True:
                try:
                    tree = next(parses)
                    if not tree or not any(tree):
                        print('CFG Parsing has failed...')
                        self.__failed_CFG_parsing_count += 1
                    else:
                        print('CFG Parsing done...')
                        print('Try to extract contracts...')
                        ans = tree.label()['CNL']
                        if self.__enable_trace:
                            print(ans)
                        if not isinstance(ans, FeatureValueTuple):
                            print('No available semantics in the parsing tree...possibly something is wrong...')
                            contracts.append(None)
                            self.__failed_CNL_collection_count += 1
                        else:
                            # Labelled Tree
                            if r := [s for s in ans if s]:
                                tmp = None
                                r = self.__normalisation(r)
                                if spec_type == SpecTypes.Parameters:
                                    tmp = self.__precondition_analysis(r, param_name)
                                elif spec_type == SpecTypes.Return:
                                    tmp = self.__postcondition_analysis(r)
                                else:
                                    tmp = self.__invariant_analyais(r, param_name)
                                contracts.append(self.__finalisation(tmp))
                        tree_count += 1
                except StopIteration:
                    print('Done with ', tree_count, ' parse trees...')
                    if tree_count == 0:
                        print('Possible Semantic extraction failure...')
                        self.__failed_CNL_collection_count += 1
                    break
        except ValueError as ve:
            self.__failed_CFG_parsing_count += 1
            print('Unsupported tokens cause the following error: ' + str(ve))
            contracts = None
        return contracts

    def __invariant_analyais(self, cnls: List[str], param_name: str) -> str:
        var = cnls[0]
        cnls = [c if c != var and c != '[**KEY**]' else param_name for c in cnls]
        # cnls = self.__normalisation(cnls)
        return '{0} {1}'.format(str(JML.Invariant), ''.join(cnls))

    def __postcondition_analysis(self, cnls: List[str]) -> str:
        # TODO: currently assume all the left operands are checking with the return value
        #       for more detail, we should have cases checking data in another classes
        if str(cnls[0]).isalnum():
            cnls[0] = str(JML.Result)
        else:
            cnls.insert(0, str(JML.Result))

        # cnls = self.__normalisation(cnls)
        return '{0} {1}'.format(str(JML.Ensures), ''.join(cnls))

    def __precondition_analysis(self, cnls: List[str], param_name: str) -> str:
        # TODO: we have to consider if the contract has any checking in the attributes
        #       currently assume all the left operands are checking with the parameter it is describing
        var = cnls[0]
        cnls = [c if c != var and c != '[**KEY**]' else param_name for c in cnls]
        # cnls = self.__normalisation(cnls)
        return '{0} {1}'.format(str(JML.Requires), ''.join(cnls))

    def __normalisation(self, cnls: List[str]) -> List[str]:
        for i, c in enumerate(cnls):
            if self.__following_operators.__contains__(c) and self.__leading_operators.__contains__(cnls[i + 1]):
                cnls.pop(i)

        return cnls

    def __finalisation(self, r: str) -> str:
        _r = r
        insert = lambda i: _r[:i] + ' ' + _r[i:]
        re1 = re.finditer(r"\w[^a-zA-Z\d+\s:.<>\[\]\-\(\)]", _r)
        c = 0
        for m in re1:
            _r = insert(m.start(0) + 1 + c)
            c += 1
            _r = insert(m.end(0) + 1 + c)
            c += 1
        return _r

    def __lexical_production(self, tags: List[Tuple]) -> List[str]:
        lex = []
        if tags:
            for tag in tags:
                token = tag[0]
                linguistic_category = tag[1]
                #if not token.isalnum() or \
                #         tag in self.__predefined_feature_lexicons:
                if tag in self.__predefined_feature_lexicons:
                    continue
                elif token in self.__useless_chars or linguistic_category in self.__useless_word_classes:
                    lex.append(linguistic_category + "[CNL=''] -> '" + token + "'")
                else:
                    lex.append(linguistic_category + "[CNL='" + token + "'] -> '" + token + "'")
        return lex

    def get_error(self):
        return { 'CFG': self.__failed_CFG_parsing_count, 'CNL': self.__failed_CNL_collection_count }
