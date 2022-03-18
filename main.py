import argparse


class Literal:
    """A literal that can be assigned a Boolean value."""
    def __init__(self, name):
        self.name = name.replace("--", "")
        self.neighbours = [] # if b is a neighbour of a, then a->b.
        self.d = None # first discovered
        self.f = None # finished examining
        self.color = None
        self.parent = None

        self.checked = False # used for second DFS
    
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
        self.dfs_time = -1
        self.dfs_topo_sorted = []
    
    def get_literal_id(self, name:str):
        '''Returns the ID of the given name in the graph, or -1 if it isn't in the graph.'''
        for i in range(len(self.literals)):
            if self.literals[i].name == name:
                return i
        return -1

    def add_literal(self, literal:Literal):
        '''Adds a new literal and its negation to the implication graph.'''
        literal = Literal(literal.name)
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
        i1 = self.get_literal_id(lt1.name)
        i2 = self.get_literal_id(lt2.name)
        if (i1 >= 0) and (i2 >= 0) and not (i1 == i2):
            self.literals[i1].add_neighbour(self.literals[i2])

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

    def dfs_init(self):
        '''initialises values for DFS'''
        for lt in self.literals:
            lt.color = "white"
            lt.parent = None
        self.dfs_time = 0

    
    def dfs_first(self, start:str=None):
        '''Conducts DFS on this graph. Returns a list of DFS trees.'''
        # start from start if it's given, otherwise just start from first literal
        ret = []
        if start:
            start_lt = self.literals[self.get_literal_id(start)]
            self.dfs_visit(start_lt)
            ret.append(start)
        for lt in self.literals:
            if lt.color == "white":
                self.dfs_visit(lt)
                ret.append(lt)
        
        return ret
    
    def dfs_second(self, start:str=None):
        '''Conducts DFS on this graph. Returns the SCCs of the graph.'''
        # start from start if it's given, otherwise just start from first literal
        ret = []
        if start:
            start_lt = self.literals[self.get_literal_id(start)]
            self.dfs_visit(start_lt)
        for lt in self.literals:
            if lt.color == "white":
                self.dfs_visit(lt)
        
        sorted_elems = self.dfs_topo_sorted
        current_list = []
        for elem in sorted_elems:
            if not elem.checked:
                elem.checked = True
                cur_elem = elem
                while cur_elem:
                    current_list.append(cur_elem)
                    cur_elem.checked = True
                    cur_elem = cur_elem.parent
                ret.append(current_list)
                current_list = []
        return ret

    def dfs_visit(self, lt):
        self.dfs_time += 1
        lt.d = self.dfs_time
        lt.color = "grey"
        for v in lt.neighbours:
            if v.color == "white":
                v.parent = lt
                self.dfs_visit(v)
        lt.color = "BLACK"
        self.dfs_time += 1
        lt.f = self.dfs_time
        self.dfs_topo_sorted.append(lt)



def main(args):
    file = open(args.file, 'r')
    file_raw_lines = file.readlines()
    file.close()

    G = Implication_Graph()
    G_inv = Implication_Graph()

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
                        raise RuntimeError("Program only supports 2-SAT clauses.")
                    elif len(current_clause) == 2:
                        #  A OR  B gives !A ->  B, !B ->  A (i.e. !( A) ->  B, !( B) ->  A)
                        # !A OR  B gives  A ->  B, !B -> !A (i.e. !(!A) ->  B, !( B) -> !A)
                        #  A OR !B gives !A -> !B,  B ->  A (i.e. !( A) -> !B, !(!B) ->  A)
                        G.add_implication(current_clause[0].get_negation(), current_clause[1])
                        G.add_implication(current_clause[1].get_negation(), current_clause[0])
                        G_inv.add_implication(current_clause[1], current_clause[0].get_negation())
                        G_inv.add_implication(current_clause[0], current_clause[1].get_negation())
                    # then reset current_clause
                    current_clause = []
                else:
                    lt = Literal(line_part)
                    G.add_literal(lt)
                    G_inv.add_literal(lt)
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
    
    G.dfs_init()
    G_inv.dfs_init()
    second_dfs_order = G.dfs_first()
    sccs = []
    for lt in second_dfs_order:
        lt_name = lt.name
        lt_id_in_second = G_inv.get_literal_id(lt_name)
        lt_in_second = G_inv.literals[lt_id_in_second]
        if lt_in_second.color == "white":
            sccs += G_inv.dfs_second(lt_in_second.name)
    
    for scc in sccs:
        pos = []
        neg = []
        for lt in scc:
            if lt.name[0] == "-":
                neg.append(lt.name)
                if lt.get_negation().name in pos:
                    print("UNSATISFIABLE")
                    return
            else:
                pos.append(lt.name)
                if lt.get_negation().name in neg:
                    print("UNSATISFIABLE")
                    return
    print("SATISFIABLE")

    bindings = {}
    variables = []
    for lt in G.literals:
        variable = lt.name
        if lt.name[0] == "-":
            variable = lt.get_negation().name
        bindings[variable] = None
        if variable not in variables:
            variables.append(variable)
    variables.sort()

    # override
    for i in range(len(sccs)-1, -1, -1):
        scc = sccs[i]
        for lt in scc:
            variable = lt.name
            value = True
            if lt.name[0] == "-":
                variable = lt.get_negation().name
                value = False
            if bindings[variable] is None:
                bindings[variable] = value
    final_report = ""
    for var in variables:
        if bindings[var]:
            final_report += "1 "
        else:
            final_report += "0 "
    print(final_report)

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("file", help = "Required .cnf file")

    args = parser.parse_args()
    main(args)