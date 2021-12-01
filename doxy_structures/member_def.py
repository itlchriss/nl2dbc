import bs4
from bs4 import NavigableString


class MemberDef:
    id = None
    kind = None
    protection = None
    static = None
    type = None
    definition = None
    argsstring = None
    name = None
    signature = None
    briefdescription = None
    detaileddescription = None
    inbodydescription = None

    def __init__(self, xml):
        self.id = xml['id']
        self.kind = xml['kind']
        self.protection = xml['prot']
        self.static = xml['static']
        self.type = xml.find('type').string
        self.definition = xml.find('definition').string
        self.argsstring = xml.find('argsstring').string
        self.name = xml.find('name').string

        self.signature = ' '.join([self.protection,
                                   "static" if self.static != "no" else "",
                                   self.type if self.type else "",
                                   self.name
                                   ])
        if self.kind == "function":
            self.signature += self.argsstring
        self.signature += ";"

        if xml.find('briefdescription'):
            self.briefdescription = xml.find('briefdescription').get_text(separator=' ', strip=True)
        if xml.find('detaileddescription'):
            dd = xml.find('detaileddescription')
            if dd.find('simplesect', { 'kind': 'since'}):
                dd.find('simplesect', { 'kind': 'since'}).decompose()
            self.detaileddescription = dd.get_text(separator=' ', strip=True)
        if xml.find('inbodydescription'):
            self.inbodydescription = xml.find('inbodydescription').get_text(separator=' ', strip=True)

    def _remove_nested_tags(self, node):
        if not node:
            pass
        elif type(node) == bs4.element.NavigableString:
            if node and node not in "\r\t\n":
                return node
            else:
                pass
        else:
            if len(node.contents) == 1:
                return self._remove_nested_tags(node.contents[0])
            elif len(node.contents) > 1:
                return list(map(self._remove_nested_tags, node.children))
