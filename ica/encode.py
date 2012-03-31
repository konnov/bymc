# State encoding from human-readable format to internal representation.
#
# There are two stages of encoding. On the first stage enumerable types
# are encoded by ranges [0..len(type)-1] and each state is represented
# by encoded values of enumerable types (still readable representation).
# On the second stage all states are enumerated and encoded by integers.
#
# For now, only the first stage is implemented.
#
# Igor Konnov, 07/2005

from cheaps.core.types import EnumType

class ProcessVariables:
    """Keeps variables types. Encodes process state to string."""

    def __init__(self):
        self._var_names = []
        self._var_types = {}

    def add_var(self, name, type):
        if name in self._var_names:
            raise "Variable " + name + " already registered"

        self._var_names.append(name)
        self._var_types[name] = type

    def get_var_types(self):
        return self._var_types

    def get_var_type(self, name):
        if name in self._var_types.keys():
            return self._var_types[name]
        else:
            print "Process vars: " + str(self._var_types.keys())
            raise "Variable " + name + " not found"

    def get_var_index(self, name):
        if name in self._var_names:
            return self._var_names.index(name)
        else:
            raise "Variable " + name + " not found"

    def get_var_names(self):
        return self._var_names

    def get_var_name(self, index):
        return self._var_names[index]

    def encode(self, values):
        """Encodes a list of pairs (var_name, var_value) to string."""
        assert(len(values) == len(self._var_names))

        # Check vars.
        for var_name in values.keys():
            if var_name not in self._var_names:
                raise "Unknown variable " + name

        encoded = ""

        for var_name in self._var_names:
            var_value = values[var_name]
            var_type = self._var_types[var_name]
            encoded += var_type.encode(var_value)
        
        return encoded

    def split_encoded(self, encoded):
        values = []
        pos = 0
        for var_name in self._var_names:
            var_type = self._var_types[var_name]
            char_len = var_type.char_len()
            encoded_value = encoded[pos : pos + char_len]
            values.append(encoded_value)
            pos += char_len
        
        return tuple(values)

    def split_and_decode(self, encoded):
        values = []
        pos = 0
        for var_name in self._var_names:
            var_type = self._var_types[var_name]
            char_len = var_type.char_len()
            encoded_value = encoded[pos : pos + char_len]
            values.append(var_type.decode(encoded_value))
            pos += char_len
        
        return tuple(values)
