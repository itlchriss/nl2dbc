from bs4 import BeautifulSoup

from doxy_structures.function_def import FunctionDef
from doxy_structures.variable_def import VariableDef

from typing import List, Dict


class SpecificationExtraction:
    raw = None
    # methods = []
    functions: List[FunctionDef] = []
    attributes: List[VariableDef] = []
    # For quick access of the function names
    # Key: name of the class. Value: list of functions in the class
    class_def = {}
    parent = None
    class_signature = None
    # A list for quick access of all the names of the software elements in the class
    __element_list = []

    __element_names = {}
    class_name = None

    def __init__(self):
        self.raw = None
        self.functions = []
        self.attributes = []
        self.class_def = {}
        self.class_signature = None

    # TODO: the path should be a folder path. Because a software can have many classes
    #       each class produces an xml file with "classjava" string as prefix
    def __read_file__(self, path):
        if not path:
            print("empty document path is provided")
        else:
            tmp = None
            with open(path, encoding='utf-8') as fp:
                tmp = fp.read()
                self.raw = BeautifulSoup(tmp, 'xml')

    # TODO: read all files and process them into one dictionary
    def parse_doxygen_req(self, path):
        self.__read_file__(path)
        if not self.raw.find('compoundname') or not self.raw.find('compounddef'):
            print('no compoundname tag is found. no class name can be extracted...exit')
            exit(2)
        else:
            self.class_name = self.raw.find('compoundname').get_text()
            class_prot = self.raw.find('compounddef')["prot"]
            self.class_signature = class_prot + " class " + self.class_name
        if self.raw.find('basecompoundref'):
            self.parent = self.raw.find('basecompoundref').get_text()
            # TODO: we need to make a configuration to deal with the template expression -- templateparamlist
            if '<' in self.parent:
                self.parent = self.parent.split('<')[0]
        # TODO: we need to make a configuration for the delimiter of the class name
        self.class_name = self.class_name.split('::')[-1]
        list_of_all_members = self.raw.find('listofallmembers').findChildren(recursive=False)
        if not list_of_all_members:
            print("no list of member is found...aborting...")
            exit(3)
        tmp = [[f.find('name').text for f in list_of_all_members]]
        for member in list_of_all_members:
            tmp.append({'prot': member['prot'], 'virt': member['virt'], 'name': member.find('name').text})
        self.class_def[self.class_name] = tmp

        list_of_functions = self.raw.find_all('memberdef', {'kind': 'function'})
        if not list_of_functions:
            print("no list of member function definitions")
        else:
            for function_def in list_of_functions:
                fd = FunctionDef(function_def)
                self.functions.append(fd)

        list_of_variables = self.raw.find_all('memberdef', { 'kind': 'variable'})
        if not list_of_variables:
            print('no list of member variable definitions')
        else:
            for variable_def in list_of_variables:
                vd = VariableDef(variable_def)
                self.attributes.append(vd)

    def get_element_list(self) -> List[str]:
        self.__element_list.append(self.class_name)
        self.__element_list.extend(self.class_def[self.class_name][0])
        return self.__element_list

    def get_element_names(self) -> Dict[str, str]:
        self.__element_names[self.class_name] = 'CLASS_' + self.class_name
        funcs = self.class_def[self.class_name][0]
        for f in funcs:
            self.__element_names[f] = 'FUNC_' + f
        return self.__element_names
