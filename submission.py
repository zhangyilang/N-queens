import copy
from csp import CSP


def create_n_queens_csp(n=8):
    """Create an N-Queen problem on the board of size n * n.

    You should call csp.add_variable() and csp.add_binary_factor().

    Args:
        n: int, number of queens, or the size of one dimension of the board.

    Returns
        csp: A CSP problem with correctly configured factor tables
        such that it can be solved by a weighted CSP solver
    """
    csp = CSP()
    # TODO: Problem a
    # TODO: BEGIN_YOUR_CODE
    for i in range(n):
        csp.add_variable('Q' + str(i), list(range(n)))    # the position of a queen in each row (from 0 to n-1)
    for i in range(n-1):
        for j in range(i+1, n):
            csp.add_binary_factor('Q' + str(i), 'Q' + str(j), lambda x, y: x != y)
            csp.add_binary_factor('Q' + str(i), 'Q' + str(j), lambda x, y: abs(x-y) != abs(j-i))
    # TODO: END_YOUR_CODE
    return csp


class BacktrackingSearch:
    """A backtracking algorithm that solves CSP.

    Attributes:
        num_assignments: keep track of the number of assignments
            (identical when the CSP is unweighted)
        num_operations: keep track of number of times backtrack() gets called
        first_assignment_num_operations: keep track of number of operations to
            get to the very first successful assignment (maybe not optimal)
        all_assignments: list of all solutions found

        csp: a weighted CSP to be solved
        mcv: bool, if True, use Most Constrained Variable heuristics
        ac3: bool, if True, AC-3 will be used after each variable is made
        domains: dictionary of domains of every variable in the CSP

    Usage:
        search = BacktrackingSearch()
        search.solve(csp)
    """

    def __init__(self):
        self.num_assignments = 0
        self.num_operations = 0
        self.first_assignment_num_operations = 0
        self.all_assignments = []

        self.csp = None
        self.mcv = False
        self.ac3 = False
        self.domains = {}

    def reset_results(self):
        """Resets the statistics of the different aspects of the CSP solver."""
        self.num_assignments = 0
        self.num_operations = 0
        self.first_assignment_num_operations = 0
        self.all_assignments = []

    def check_factors(self, assignment, var, val):
        """Check consistency between current assignment and a new variable.

        Given a CSP, a partial assignment, and a proposed new value for a
        variable, return the change of weights after assigning the variable
        with the proposed value.

        Args:
            assignment: A dictionary of current assignment.
                Unassigned variables do not have entries, while an assigned
                variable has the assigned value as value in dictionary.
                e.g. if the domain of the variable A is [5,6],
                and 6 was assigned to it, then assignment[A] == 6.
            var: name of an unassigned variable.
            val: the proposed value.

        Returns:
            bool
                True if the new variable with value can satisfy constraint,
                otherwise, False
        """
        assert var not in assignment
        if self.csp.unary_factors[var]:
            if self.csp.unary_factors[var][val] == 0:
                return False
        for var2, factor in self.csp.binary_factors[var].items():
            if var2 not in assignment:
                continue
            if factor[val][assignment[var2]] == 0:
                return False
        return True

    def solve(self, csp, mcv=False, ac3=False):
        """Solves the given unweighted CSP using heuristics.

        Note that we want this function to find all possible assignments.
        The results are stored in the variables described in
            reset_result().

        Args:
            csp: A unweighted CSP.
            mcv: bool, if True, Most Constrained Variable heuristics is used.
            ac3: bool, if True, AC-3 will be used after each assignment of an
            variable is made.
        """
        self.csp = csp
        self.mcv = mcv
        self.ac3 = ac3
        self.reset_results()
        self.domains = {var: list(self.csp.values[var])
                        for var in self.csp.variables}
        self.backtrack({})

    def backtrack(self, assignment):
        """Back-tracking algorithms to find all possible solutions to the CSP.

        Args:
            assignment: a dictionary of current assignment.
                Unassigned variables do not have entries, while an assigned
                variable has the assigned value as value in dictionary.
                    e.g. if the domain of the variable A is [5, 6],
                    and 6 was assigned to it, then assignment[A] == 6.
        """
        self.num_operations += 1
        num_assigned = len(assignment.keys())
        if num_assigned == self.csp.vars_num:
            self.num_assignments += 1
            new_assignment = {}
            for var in self.csp.variables:
                new_assignment[var] = assignment[var]
            self.all_assignments.append(new_assignment)
            if self.first_assignment_num_operations == 0:
                self.first_assignment_num_operations = self.num_operations
            return

        var = self.get_unassigned_variable(assignment)
        ordered_values = self.domains[var]

        if not self.ac3:
            for value in ordered_values:
                if self.check_factors(assignment, var, value):
                    assignment[var] = value
                    self.backtrack(assignment)
                    del assignment[var]
        else:
            for value in ordered_values:
                if self.check_factors(assignment, var, value):
                    assignment[var] = value
                    local_copy = copy.deepcopy(self.domains)
                    self.domains[var] = [value]
                    self.arc_consistency_check(var)
                    self.backtrack(assignment)
                    self.domains = local_copy
                    del assignment[var]

    def get_unassigned_variable(self, assignment):
        """Get a currently unassigned variable for a partial assignment.

        If mcv is True, Use heuristic: most constrained variable (MCV)
        Otherwise, select a variable without any heuristics.

        Most Constrained Variable (MCV):
            Select a variable with the least number of remaining domain values.
            Hint: self.domains[var] gives you all the possible values
            Hint: get_delta_weight gives the change in weights given a partial
                assignment, a variable, and a proposed value to this variable
            Hint: choose the variable with lowest index in self.csp.variables
                for ties

        Args:
            assignment: a dictionary of current assignment.

        Returns
            var: a currently unassigned variable.
        """
        if not self.mcv:
            for var in self.csp.variables:
                if var not in assignment:
                    return var
        else:
            # TODO: Problem b
            # TODO: BEGIN_YOUR_CODE
            min_num = float('inf')  # store the least number of remaining domain values
            min_var = None          # variable corresponding to `min_num`
            for var in self.csp.variables:
                if var in assignment:
                    continue
                num = 0
                for val in self.domains[var]:
                    if self.check_factors(assignment, var, val):
                        num += 1
                if num < min_num:
                    min_num = num
                    min_var = var
            return min_var
            # TODO: END_YOUR_CODE

    def arc_consistency_check(self, var):
        """AC-3 algorithm.

        The goal is to reduce the size of the domain values for the unassigned
        variables based on arc consistency.

        Hint: get variables neighboring variable var:
            self.csp.get_neighbor_vars(var)

        Hint: check if a value or two values are inconsistent:
            For unary factors
                self.csp.unaryFactors[var1][val1] == 0
            For binary factors
                self.csp.binaryFactors[var1][var2][val1][val2] == 0

        Args:
            var: the variable whose value has just been set
        """
        # TODO: Problem c
        # TODO: BEGIN_YOUR_CODE
        def remove_inconsistent_values(var1, var2):  # arc consistence from var1 to var2
            removed = False
            for val1 in list(self.domains[var1]):
                consistent = False
                for val2 in self.domains[var2]:
                    if self.csp.binary_factors[var1][var2][val1][val2]:
                        consistent = True
                        break
                if not consistent:
                    self.domains[var1].remove(val1)
                    removed = True
            return removed

        queue = [(neighbor, var) for neighbor in self.csp.get_neighbor_vars(var)]   # initialization
        while len(queue):
            var1, var2 = queue.pop(0)
            if remove_inconsistent_values(var1, var2):
                if len(self.domains[var1]) == 0:    # No solution under this assignment
                    for var0 in self.csp.variables:
                        self.domains[var0] = []
                    return
                queue += [(neighbor, var1) for neighbor in self.csp.get_neighbor_vars(var1)]
        # TODO: END_YOUR_CODE
