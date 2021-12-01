import getopt
import re
import sys
from typing import List

from doxy_structures.function_def import FunctionDef
from doxy_structures.variable_def import VariableDef
from pipeline.cleansing import Cleansing
from pipeline.contract_generation import ContractGeneration
from pipeline.enum.contract_types import SpecTypes
from pipeline.specification_extraction import SpecificationExtraction

ENABLE_TRACE = 0
ENABLE_PRINT_TAGS = 0
ENABLE_PRINT_RAW_SPEC = 0


def cleansing_attribute_spec(raw_spec: List[VariableDef], cleanser: Cleansing):
    cleansed_attribute_spec_set = {}
    for v in raw_spec:
        if v.detaileddescription:
            cleansed_attribute_spec_set[v.name] = {SpecTypes.Attributes: cleanser.cleanse(v.detaileddescription)}
        else:
            cleansed_attribute_spec_set[v.name] = {}
        cleansed_attribute_spec_set[v.name][SpecTypes.Signature] = v.signature
        cleansed_attribute_spec_set[v.name][SpecTypes.Protection] = v.protection
    return cleansed_attribute_spec_set


def cleansing_function_spec(raw_spec: List[FunctionDef], cleanser: Cleansing):
    cleansed_function_spec_set = {}
    for f in raw_spec:
        param_names = []
        cleansed_param_spec_set = []
        cleansed_return_spec = None
        if f.param_specs:
            param_names = [*f.param_specs]
            for param in f.param_specs:
                cleansed_param_spec_set.append(
                    [cleanser.cleanse(f.param_specs[param], param_names), param, f.param_specs[param]])
        if f.return_specs:
            cleansed_return_spec = cleanser.cleanse(f.return_specs, param_names)
        cleansed_function_spec_set[f.name] = {SpecTypes.Parameters: cleansed_param_spec_set,
                                              SpecTypes.Return: cleansed_return_spec,
                                              SpecTypes.Signature: f.signature}
    return cleansed_function_spec_set


def generate_attribute_contract(specs, generator):
    contract_set = {}
    for vname in specs:
        spec = specs[vname]
        signature = spec[SpecTypes.Signature]
        if SpecTypes.Attributes not in spec:
            contract_set[signature] = None
        else:
            print('---Parsing invariant about ' + vname)
            inv_set = []
            for tags in spec[SpecTypes.Attributes]:
                if ENABLE_TRACE:
                    print('tags: ', tags)
                inv_set.append(generator.generate(
                    tags,
                    SpecTypes.Attributes,
                    param_name=vname
                ))
            contract_set[signature] = {'c': inv_set, 'p': specs[vname][SpecTypes.Protection]}
            if ENABLE_TRACE:
                print('resulting contract: ', inv_set)
    return contract_set


def generate_function_contract(specs, generator):
    contract_set = {}
    for fname in specs:
        print('Parsing function specification of "' + fname + '"')
        f_set = []
        spec_set = specs[fname]
        signature = spec_set[SpecTypes.Signature]
        # param_names = None
        # if pre_spec := spec_set[SpecTypes.Parameters]:
        #     param_names = {}
        #     for param_name in [p[1] for p in pre_spec]:
        #         param_names[param_name] = 'PARAM_' + param_name
        if not spec_set:
            continue
        if pre_spec := spec_set[SpecTypes.Parameters]:
            for spec in pre_spec:
                print('---Parsing precondition about ' + spec[1])
                if ENABLE_TRACE:
                    print('org. :', str(spec[2]))
                for tags in spec[0]:
                    if ENABLE_PRINT_TAGS:
                        print('tags: ', tags)
                    contract = generator.generate(
                        tags=tags,
                        spec_type=SpecTypes.Parameters, param_name=spec[1])
                    if ENABLE_TRACE:
                        print('resulting contract: ', contract)
                    f_set.append(contract)
        if post_spec := spec_set[SpecTypes.Return]:
            print('---Parsing postcondition')
            for tags in post_spec:
                if ENABLE_PRINT_TAGS:
                    print('tags: ', tags)
                contract = generator.generate(
                    tags=tags, spec_type=SpecTypes.Return)
                if ENABLE_TRACE:
                    print('resulting contract: ', contract)
                f_set.append(contract)
        contract_set[signature] = {'c': f_set, 'p': None}
    return contract_set


def write_to_file(contract_set, fp):
    for signature in contract_set:
        _set = contract_set[signature]
        if _set:
            c = _set['c']
            p = _set['p']
            for cnt in c:
                [fp.write(r"//@ " + (p if p else "") + " " + contract + ";\n") for contract in cnt]
        fp.write(signature + "\n")
        fp.write("\n")


def nl2dbc(inputfile, outputfile, grammarfile):
    print('Input file is ', inputfile)
    print('Start specification extraction from the input file...')
    spec_extractor = SpecificationExtraction()
    spec_extractor.parse_doxygen_req(inputfile)
    raw_function_spec = spec_extractor.functions
    raw_attribute_spec = spec_extractor.attributes
    class_signature = spec_extractor.class_signature
    if ENABLE_PRINT_RAW_SPEC:
        print('extracted attribute specifications: ')
        for spec in raw_attribute_spec:
            print('attribute: ', spec.signature)
            print('detail specification: ', spec.detaileddescription)
            print('brief specification: ', spec.briefdescription)
        for spec in raw_function_spec:
            print('attribute: ', spec.signature)
            print('detail specification: ', spec.detaileddescription)
            print('brief specification: ', spec.briefdescription)
        for name in spec_extractor.get_element_list():
            print(name)
    print('Finished...')
    print('Marking parameter keywords in specifications...')
    #       2. cleanser - Text Cleansing
    print('Start text cleansing in the specifications...')
    cleanser = Cleansing()
    cleansed_function_spec_set = cleansing_function_spec(raw_function_spec, cleanser)
    cleansed_attribute_spec_set = cleansing_attribute_spec(raw_attribute_spec, cleanser)
    print('Finished...')
    #       3. contract generation
    print('Start CFG Parsing...')
    generator = ContractGeneration(grammarfile, ENABLE_TRACE)
    # generator = FOLGeneration(grammarfile, spec_extractor.get_element_names(), ENABLE_TRACE)
    print('Processing with the attributes...')
    attribute_contracts = generate_attribute_contract(cleansed_attribute_spec_set, generator)
    print('Processing with the methods...')
    function_contracts = generate_function_contract(cleansed_function_spec_set, generator)
    error = generator.get_error()
    print('CFG uncovered cases: ', error['CFG'])
    print('Semantic error cases: ', error['CNL'])
    if outputfile:
        print('Writing to file...')
        with open(outputfile, encoding='utf-8', mode="w") as fp:
            fp.write(class_signature + " {\n")
            write_to_file(attribute_contracts, fp)
            write_to_file(function_contracts, fp)
            fp.write("}\n")
        print('Done...')


def main(argv):
    inputfile = ''
    outputfile = ''
    grammarfile = None
    try:
        opts, args = getopt.getopt(argv, "hi:o:g:", ["ifile=", "ofile=", "gfile"])
    except getopt.GetoptError:
        print('test.py -i <inputfile> -o <outputfile> -g <grammarfile>')
        sys.exit(2)
    for opt, arg in opts:
        if opt == '-h':
            print('test.py -i <inputfile> -o <outputfile> -g <grammarfile>')
            sys.exit()
        elif opt in ("-i", "--ifile"):
            inputfile = arg
        elif opt in ("-o", "--ofile"):
            outputfile = arg
        elif opt in ("-g", "-gfile"):
            grammarfile = arg
    #       1. specExt - Specification Extraction
    grammar = None
    with open(grammarfile, encoding='utf-8') as fp:
        grammar = fp.read()
    nl2dbc(inputfile, outputfile, grammar)


if __name__ == "__main__":
    if sys.argv[1:]:
        main(sys.argv[1:])
    else:
        print('use -h to view the helping messages')
