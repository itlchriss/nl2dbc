from bs4 import BeautifulSoup


class Method:
    protection = None
    refid = None
    virtual = False
    scope = None
    name = None

    def __init__(self, xml_member):
        self.protection = xml_member['prot']
        self.refid = xml_member['refid']
        self.virtual = xml_member['virt']
        self.scope = xml_member.find('scope').string
        self.name = xml_member.find('name').string


