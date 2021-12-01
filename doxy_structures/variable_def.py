from doxy_structures.member_def import MemberDef


class VariableDef(MemberDef):
    mutable = None
    initializer = None

    def __init__(self, xml):
        super().__init__(xml)
        self.mutable = xml['mutable']
        if xml.find('initializer'):
            self.initializer = xml.find('initializer').string

