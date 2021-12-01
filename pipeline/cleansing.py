import re
from typing import Tuple, List

from nltk.tokenize import sent_tokenize
from nltk.tokenize.stanford import StanfordTokenizer
import os
from nltk import WordNetLemmatizer, TreebankWordTokenizer, StanfordPOSTagger
from nltk.corpus import wordnet as wn
from word2number import w2n

class Cleansing:
    __lemmatizer = None
    __tokenizer = None
    __tagger = None
    __punctuations = ";,'()\\."
    __replacement_rules = {
        'not': ['ain', 'aren', "aren't", 'couldn', "couldn't", 'didn', "didn't", 'doesn', "doesn't", 'hadn', "hadn't",
                'hasn', "hasn't", 'haven', "haven't", 'isn', "isn't", 'ma', 'mightn', "mightn't", 'mustn', "mustn't",
                'needn', "needn't", 'shan', "shan't", 'shouldn', "shouldn't", 'wasn', "wasn't", 'weren', "weren't",
                'won', "won't", 'wouldn', "wouldn't", 'don', "don't", 'not', 'cannot']
    }
    __stopwords = ['shall', 'should', 'can', 'could', 'may', 'might', 'will', 'would', 'ought', 'dare', 'need', 'must',
                   'does', 'do', 'did']

    __stopword_rules = {
        'been': ['have', 'has', 'had'],
        'being': ['is', 'am', 'are', 'was', 'were']
    }

    def __init__(self):
        self.__lemmatizer = WordNetLemmatizer()
        # self.__tokenizer = TreebankWordTokenizer()
        PIPELINE_DIR = os.path.dirname(os.path.abspath(__file__))
        _path_to_model = PIPELINE_DIR + '/../utility/english-bidirectional-distsim.tagger'
        _path_to_jar = PIPELINE_DIR + '/../utility/stanford-postagger-4.2.0.jar'
        # if not os.getenv('JAVAHOME'):
        #     print('No JAVAHOME...Setting Environment')
        #     os.environ["JAVAHOME"] = "C:\\Program Files\\Java\\jdk-16\\bin"
        #     print('Done...Set JAVAHOME as ' + os.environ["JAVAHOME"])
        self.__tagger = StanfordPOSTagger(_path_to_model, _path_to_jar)
        self.__tokenizer = StanfordTokenizer(_path_to_jar)

    # def cleanse(self, sentence: str, special_markings: List[str] = None) -> Tuple[List[str], List[Tuple]]:
    # def cleanse(self, text: str, special_markings: List[str] = None) -> Tuple[List[List[str]], List[List[Tuple]]]:
    def cleanse(self, text: str, special_markings: List[str] = None) -> List[List[Tuple]]:
        text = text.lower()
        sentences = sent_tokenize(text)
        # token_bucket = []
        tag_bucket = []
        for sentence in sentences:
            tokens = self.__tokenisation(sentence)
            tokens = self.__word_replacement(tokens)
            tokens = self.__character_removal(tokens)
            # tokens = self.__stopwords_removal(tokens)
            tokens = self.__normalisation(tokens)
            tags = self.__part_of_speech_tagging(tokens)
            # TODO: may be we can have a better name
            tags = self.__stopwords_removal(tags)
            tags = self.__lemmatization(tags)
            tags = self.__word_massaging(tags)
            tags = self.__marking_params(tags, special_markings)
            tags = self.__post_analysis(tags)
            # token_bucket.append([t[0] for t in tags])
            tag_bucket.append(tags)
        # return [t[0] for t in tags], tags
        # return token_bucket, tag_bucket
        return tag_bucket

    def __word_massaging(self, tags: List[Tuple[str, str]]):
        _tags = tags
        c = len(_tags) - 1
        for i, t in enumerate(_tags):
            if i == c:
                break
            token, cat = t
            if cat in ['NN', 'JJ', 'VBG'] and _tags[i + 1][1] == 'NN':
                new_token = token + '_' + _tags[i + 1][0]
                _tags.pop(i)
                _tags.pop(i)
                _tags.insert(i, (new_token, 'NNP'))
                c -= 1
        return _tags

    def __marking_params(self, tags: List[Tuple[str, str]], sw: List[str] = None):
        _tags = tags
        if not sw:
            return _tags
        iterator = enumerate(_tags)
        for i, t in iterator:
            if t in sw:
                _tags.insert(i, ('[', "-LRB-"))
                _tags.insert(i + 2, (']', "-RRB-"))
                [next(iterator, None) for _ in range(2)]
        return _tags

    def __normalisation(self, tokens: List[str]) -> List[str]:
        # print('before norm: ', tokens)
        iterator = enumerate(tokens)
        for i, t in iterator:
            if t.__contains__("-") and len(t) > 1:
                # Negative number normalisation
                if t.lstrip("-").isnumeric() and len(t) > 1:
                    x = t.lstrip("-")
                    tokens.pop(i)
                    tokens.insert(i, "-")
                    tokens.insert(i + 1, x)
                    [next(iterator, None) for _ in range(2)]
                else:
                    x = t
                    tokens.pop(i)
                    x = re.split('(-)', x)
                    [tokens.insert(i + j, x[j]) for j in range(len(x))]
                    [next(iterator, None) for _ in range(len(x))]
            # in case the tokenizer does not tokenize properly
            if t[-1] == "." and len(t) > 1:
                tokens[i] = t[:-1]
                
        return tokens

    def __penn2morphy(self, penntag: str) -> str:
        if penntag.startswith('NN'):
            return wn.NOUN
        #elif penntag.startswith('VB'):
        elif penntag in ['VBZ', 'VBD', 'VBP', 'VB']:
            return wn.VERB
        elif penntag.startswith('JJ'):
            return wn.ADJ
        elif penntag.startswith('RB'):
            return wn.ADV
        else:
            return ''

    def __part_of_speech_tagging(self, tokens: List[str]) -> List[Tuple]:
        return self.__tagger.tag(tokens)

    def __tokenisation(self, sentence: str) -> List[str]:
        # print('org sentence: ', sentence)
        return self.__tokenizer.tokenize(sentence)

    def __word_replacement(self, tokens: List[str]) -> List[str]:
        for word in self.__replacement_rules:
            rlist = self.__replacement_rules[word]
            tokens = [word if tokens[i].lower() in rlist else tokens[i] for i in range(len(tokens))]
        return tokens

    def __character_removal(self, tokens: List[str]) -> List[str]:
        tokens = [tokens[i] for i in range(len(tokens)) if tokens[i] not in self.__punctuations]
        return tokens

    def __stopwords_removal(self, tags: List[Tuple[str, str]]) -> List[Tuple[str, str]]:
        to_be_removed_indices = []
        tokens = [t[0] for t in tags]
        for i in range(1, len(tokens)):
            if tokens[i] in self.__stopword_rules and tokens[i - 1] in self.__stopword_rules[tokens[i]]:
                to_be_removed_indices.append(i)
                to_be_removed_indices.append(i - 1)
        tags = [t for j, t in enumerate(tags) if j not in to_be_removed_indices]
        tags = [t for t in tags if t[0] not in self.__stopwords]
        return tags

    def __lemmatization(self, tags: List[Tuple[str, str]]) -> List[Tuple[str, str]]:
        _tags = tags
        for i, t in enumerate(tags):
            penntag = t[1]
            wntag = self.__penn2morphy(penntag)
            if wntag:
                _tags[i] = (self.__lemmatizer.lemmatize(t[0], pos=wntag), t[1][0:2])
            elif penntag in ['VBN', 'VBG']:
                _tags[i] = (self.__lemmatizer.lemmatize(t[0], pos=wn.VERB), penntag)
        return _tags

    def __post_analysis(self, tags: List[Tuple[str, str]]) -> List[Tuple[str, str]]:
        _tags = tags

        for i, t in enumerate(tags):
            # a dash can mean 'or' if and only if LHS and RHS are both with the same word type
            if t[0] == '/' and tags[i - 1][1][0:2] == tags[i + 1][1][0:2]:
               _tags[i] = ("or", "CC")
            # a number is indicated but the number is written in text
            if t[1] == 'CD' and t[0].isalpha():
               _tags[i] = (str(w2n.word_to_num(t[0])), 'CD')
        return _tags
