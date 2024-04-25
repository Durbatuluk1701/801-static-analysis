class Equality:
    def __eq__(self, other):
        return isinstance(other, self.__class__) and self.__dict__ == other.__dict__

    def __ne__(self, other):
        return not self.__eq__(other)

    def to_str(self, tabNum: int) -> str:
        return ""

    def eval(self, env):
        pass
