from doxy_structures.member_def import MemberDef
from doxy_structures.param_def import ParamDef


class FunctionDef(MemberDef):
    inline = None
    virt = None
    explicit = None
    const = None
    param_decl = []
    param_specs = {}
    return_specs = None

    def __init__(self, xml):
        super().__init__(xml)
        self.inline = xml['inline']
        self.virt = xml['virt']
        self.explicit = xml['explicit']
        self.const = xml['const']

        params = xml.find_all('param')
        if params:
            self.param_decl = []
            for param in params:
                self.param_decl.append(ParamDef(param))

        dd = xml.find('detaileddescription')
        if dd.find('parameterlist', {'kind': 'param'}):
            self.param_specs = {}
            param_items = xml.find('detaileddescription').find('parameterlist', {'kind': 'param'}).find_all('parameteritem')
            for param in param_items:
                item_name = param.find('parametername').text
                item_desc = param.find('parameterdescription').get_text(separator=' ')
                if item_name:
                    self.param_specs[item_name] = item_desc.strip() if item_desc else ''

        returns = xml.find('detaileddescription').find('simplesect', {'kind': 'return'})
        if returns:
            para = returns.find('para')
            if para:
                self.return_specs = para.get_text(separator=' ')



