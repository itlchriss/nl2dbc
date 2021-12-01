class ParamDef:
    type = None
    declname = None

    def __init__(self, xml):
        self.type = xml.find('type').string
        self.declname = xml.find('declname').string