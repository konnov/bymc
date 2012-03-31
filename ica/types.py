# Types of variables.
#
# Enum and bound integers are supported.
#
# Igor Konnov, 07/2005

import re

TYPE_ENUM = 1
TYPE_INT = 2

class Type:
    """Base variables type"""

    def __init__(self, type_id, type_name):
        self.id = type_id
        self.name = type_name

    def get_type_id(self):
        return self.id

    def get_type_name(self):
        return self.name

    def has_value(self):
        raise "Not implemented in abstract type"

    def encode(self, value):
        raise "Not implemented in abstract type"

    def decode(self, value):
        raise "Not implemented in abstract type"

    def char_len():
        raise "Not implemented in abstract type"

    def declaration_str():
        raise "Not implemented in abstract type"


class EnumType(Type):
    """Enumerable type"""

    def __init__(self):
        Type.__init__(self, TYPE_ENUM, "Enum")

        self._values = []
        self._dig_len = 0
        # if all enum values contain single character?
        self._is_single_char = True

    def get_values(self):
        return self._values

    def add_value(self, value):
        if not re.compile("[a-zA-Z_][a-zA-Z0-9_]*").match(value):
            raise "Enumeration value must be a valid identifier (" + str(value) + " passed)"
            
        if not re.compile("^[a-zA-Z]$").match(value):
            self._is_single_char = False
        
        if value not in self._values:
            self._values.append(value)

        self._dig_len = _len_in_digits(len(self._values) - 1)

    def has_value(self, value):
        return value in self._values

    def encode(self, value):
        """Get index of value.

           Raises IndexError if value is unknown"""

        if self._is_single_char:
            # single char is not encoded
            return value
        else:
            return str(self._values.index(value)).zfill(self._dig_len)

    def decode(self, encoded_val):
        if encoded_val.isalpha() and len(encoded_val) == 1:
            # single char is not encoded
            return encoded_val

        if int(encoded_val) >= len(self._values):
            print "values = %s, index = %d, encoded = %s"\
                % (str(self._values), int(encoded_val), encoded_val)
            
        return self._values[int(encoded_val)]

    def char_len(self):
        if self._is_single_char:
            return 1
        else:
            return self._dig_len

    def declaration_str(self):
        i = 1
        cnt = len(self._values)

        str = "enum { "
        for v in self._values:
            str += v
            if i != cnt:
                str += ", "
            else:
                str += "}"

            i += 1 

        return str


class IntegerType(Type):
    """Integer type. In fact, it operates as an enumerable."""

    def __init__(self): 
        Type.__init__(self, TYPE_INT, "Integer")

        self._range = (0, -1)
        self_dig_len = 1

    def get_values(self):
        return range(self._range[0], self._range[1] + 1)

    def add_value(self, value):
        int_val = int(value)

        if self._range == None:
            self._range = (int_val, int_val)
        else:
            self._range = (min(self.get_low(), int_val),
                           max(self.get_high(), int_val))

        self._dig_len = _len_in_digits(self.get_high() - self.get_low() + 1)

    def has_value(self, value):
        return value >= self.get_low() and value <= self.get_high()

    def get_low(self):
        return self._range[0]

    def get_high(self):
        return self._range[1]

    def encode(self, value):
        """Get index of value.

           Raises IndexError if value is unknown"""

        return str(int(value) - self.get_low()).zfill(self._dig_len)

    def decode(self, encoded_val):
        return int(encoded_val)

    def char_len(self):
        return self._dig_len

    def declaration_str(self):
        return "int"


def _len_in_digits(value):
    l = 1
    upper = 10
    
    while value >= upper:
        upper = 10 * upper
        l += 1

    return l
