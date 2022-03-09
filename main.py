import argparse
from collections import deque # stack for DFS


class Literal:
    """A literal that can be assigned a Boolean value."""
    def __init__(self, name):
        self.name = name.replace("--", "")
        self.neighbours = [] # if b is a neighbour of a, then a->b.
    
    def get_negation(self):
        '''Returns the negation of this literal.'''
        return Literal("-" + self.name)

    def __eq__(self, other):
        return self.name == other.name

    def add_neighbour(self, lt):
        '''Sets the given literal lt as a neighbour of this literal.'''
        self.neighbours.append(lt)

    def __str__(self):
        return self.name

    def __repr__(self):
        return "Literal: " + self.name

class Implication_Graph:
    """An implication graph that contains a series of implications between Literals."""
    def __init__(self):
        self.literals = []
        self.bindings = {}
    
    def get_literal_id(self, name:str):
        '''Returns the ID of the given name in the graph, or -1 if it isn't in the graph.'''
        try:
            i = self.literals.index(name)
            return i
        except ValueError:
            return -1

    def add_literal(self, literal:Literal):
        '''Adds a literal and its negation to the implication graph.'''
        if not literal in self:
            self.literals.append(literal)
            self.literals.append(literal.get_negation())
            self.bindings[literal.name] = None
            self.bindings[literal.get_negation().name] = None

    def add_forced(self, lt:Literal):
        '''Adds a literal that MUST evaluate to True for the problem to be satisfiable.'''
        self.bindings[lt.name] = True
        self.bindings[lt.get_negation().name] = False

    def add_implication(self, lt1:Literal, lt2:Literal):
        '''Adds the following relation to the implication graph: lt1 -> lt2. Throws RuntimeError if invalid operation.'''
        # locate the relevant literals in self.literals
        i1 = self.get_literal_id(lt1)
        i2 = self.get_literal_id(lt2)
        if (i1 >= 0) and (i2 >= 0) and not (i1 == i2):
            self.literals[i1].add_neighbour(self.literals[i2])
        else:
            raise RuntimeError("Invalid add_implication operation.")


    def get_implications(self)->str:
        '''Returns a readable String of the implications'''
        ret = ""
        for lt in self.literals:
            lt_str = lt.name
            for neighbour in lt.neighbours:
                lt_str += " -> " + neighbour.name
                ret += lt_str + "\n"
                lt_str = lt.name
        return ret

    
    def __contains__(self, literal:Literal):
        for lt in self.literals:
            if lt.name == literal.name:
                return True
        return False

    def __str__(self):
        ret = "["
        if len(self.literals) > 0:
            ret += str(self.literals[0])
            for i in range(1, len(self.literals)):
                ret += "," + str(self.literals[i])
        ret += "]"
        return ret
    
    def get_path(self, start:Literal)->list:
        '''Returns a list of nodes that are strongly connected starting from start. Returns None if there is no such strongly connected path.'''
        # i.e.: DFS from start all the way back to start.
        # TODO: Change to: actually should search ALL strongly connected paths, and return bad if there's one that has both lit and neg
        ret = []
        node:Literal = self.literals[self.get_literal_id(start)]
        q = deque(node.neighbours)
        while len(q) > 0:
            node = q.pop()
            if node == start:
                ret.append(node)
                return ret
            if node in ret:
                continue
            ret.append(node)
            for neighbour in node.neighbours:
                if neighbour.get_negation() in ret:
                    continue
                q.append(neighbour)
        return ret


def main(args):
    file = open(args.file, 'r')
    file_raw_lines = file.readlines()
    file.close()

    G = Implication_Graph()

    # Handling reading lines beyond preamble
    read_mode = False # True after program statement has been read
    current_clause = [] # list containing the current clause


    # Read line by line
    for line in file_raw_lines:
        line = line.strip(" \n")
        # skip empty lines
        if line == "":
            continue

        if read_mode:
            # process each line
            line_parts = line.split(" ")
            for line_part in line_parts:
                if line_part == "0":
                    # parse current_clause, add the implication
                    if len(current_clause) > 2:
                        raise RuntimeError("Program does not support clauses with more than two literals.")

                    if len(current_clause) == 1:
                        G.add_forced(current_clause[0])
                    elif len(current_clause) == 2:
                        #  A OR  B gives !A ->  B, !B ->  A (i.e. !( A) ->  B, !( B) ->  A)
                        # !A OR  B gives  A ->  B, !B -> !A (i.e. !(!A) ->  B, !( B) -> !A)
                        #  A OR !B gives !A -> !B,  B ->  A (i.e. !( A) -> !B, !(!B) ->  A)
                        G.add_implication(current_clause[0].get_negation(), current_clause[1])
                        G.add_implication(current_clause[1].get_negation(), current_clause[0])
                    # then reset current_clause
                    current_clause = []
                else:
                    lt = Literal(line_part)
                    G.add_literal(lt)
                    current_clause.append(lt)
        else:
            if line[0] == "c":
                continue
            elif line[0] == "p":
                line_parts = line.split(" ")
                if not line_parts[1] == "cnf":
                    raise RuntimeError("Program does not support non-CNF files.")
                n = int(line_parts[2]) # number of variables
                m = int(line_parts[3]) # number of clauses
                read_mode = True
    
    print(G)
    print(G.get_implications())


    

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("file", help = "Required .cnf file")

    args = parser.parse_args()
    main(args)