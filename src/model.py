from collections import namedtuple

# Variables are integers.

# Constants are integers. Variables and constants exist in the same space.

DEBUG = False
def debug_print(*args):
    if DEBUG:
        print(*args)

current_identifier = 0

constants = {0: '='}
variables = {}
var_list = []

# Create new constants or new variables.
def newconst(name = None):
    global current_identifier
    current_identifier += 1
    constants[current_identifier] = (name.upper() or 'C_{%s}' % (current_identifier,))
    return current_identifier

def newvar(name = None):
    global current_identifier
    current_identifier += 1
    variables[current_identifier] = (name.lower() or 'v_{%s}' % (current_identifier,))
    var_list.append(current_identifier)
    return current_identifier

# The entire language:
Functor = namedtuple('Functor', ('functor', 'arguments'))
Relation = namedtuple('Relation', ('relation', 'arguments'))

And = namedtuple('And', ('left', 'right'))
Or = namedtuple('Or', ('left', 'right'))
Not = namedtuple('Not', ('body',))

Universal = namedtuple('Universal', ('variable', 'body'))
Existential = namedtuple('Existential', ('variable', 'body'))

Implies = namedtuple('Implies', ('left', 'right'))
Iff = namedtuple('Iff', ('left', 'right'))

# Fix the equality relation
def correct_equality(t):
    def eq(self, other):
        return type(self) == type(other) and super(t, self).__eq__(other)
    return eq
for t in (Functor, Relation, And, Or, Not, Universal, Existential, Implies, Iff):
    t.__eq__ = correct_equality(t)

# Arguments tuple
class Args(tuple):
    def __new__(cls, *args):
        return super(Args, cls).__new__(cls, args)

    def __eq__(self, other):
        return type(self) == type(other) and super().__eq__(other)

    def __hash__(self):
        return super().__hash__()

'''
SUBSTITUTION
'''
def substitute(x, sub):
    if type(x) is int:
        return (sub[x] if x in sub else x)
    debug_print(render_tree(x))
    return type(x)(*(substitute(k, sub) for k in x))

def sub_all(x, sub):
    return frozenset(substitute(k, sub) for k in x)

def all_variables_set(term):
    if type(term) is int:
        return ({term}, [term]) if term in variables else (set(), [])
    else:
        # Enforce a consistent ordering
        if type(term) is set or type(term) is frozenset:
            term = sorted(term, key = hash)

        result_set = set()
        result = []
        for x in term:
            rset, rlist = all_variables_set(x)

            for variable in rlist:
                if variable not in result_set:
                    result_set.add(variable)
                    result.append(variable)

        return result_set, result

def all_variables(term):
    return all_variables_set(term)[1]

def canon(disjunction):
    # Remove any antireflexive statements
    disjunction = frozenset(
        x for x in disjunction
        if not (type(x) is Not
            and type(x.body) is Relation and
            x.body.relation == 0 and
            x.body.arguments[0] == x.body.arguments[1]
        )
    )

    # Confine all variables to a finite set
    variter = iter(var_list)
    return sub_all(disjunction, {x: next(variter) for x in all_variables(disjunction)})

'''
MOST GENERAL UNIFIER: returns a new expression with unification.
'''
def disagree(a, b):
    if type(a) != type(b):
        return (a, b)
    elif type(a) is not int:
        return next(
            (d for d in (disagree(x, y) for (x, y) in zip(a, b)) if d is not None),
            None
        )
    elif a != b:
        return (a, b)
    else:
        return None

def uniquify(disjunction):
    return sub_all(disjunction,
            {x: newvar(variables[x] + '\'') for x in all_variables(disjunction)}
    )

def variable_in(x, y):
    if type(y) is int:
        return x == y
    else:
        return any(variable_in(x, z) for z in y)

def mgu(a, b):
    sub = {}

    while True:
        diff = disagree(a, b)

        if diff is None:
            return sub

        if diff[0] in variables and not variable_in(diff[0], diff[1]):
            sub[diff[0]] = diff[1]
        elif diff[1] in variables and not variable_in(diff[1], diff[0]):
            sub[diff[1]] = diff[0]
        else:
            return None

        a = substitute(a, sub)
        b = substitute(b, sub)

'''
CNF: returns a set of sets of terms
'''
def strip_inference(tree):
    if type(tree) is Iff:
        # Expand equivalencies into two implications
        left = strip_inference(tree.left)
        right = strip_inference(tree.right)
        return Or(And(left, right), And(Not(left), Not(right)))

    if type(tree) is Implies:
        # Expand implications into disjunctive form
        return Or(Not(strip_inference(tree.left)), strip_inference(tree.right))

    elif type(tree) is int:
        return tree

    else:
        return type(tree)(*(strip_inference(x) for x in tree))

# Move all Nots as far into the tree as possible
def strip_negation(tree):
    if type(tree) is Not:
        # Not negates itself
        if type(tree.body) is Not:
            return strip_negation(tree.body.body)

        # And and Or switch
        if type(tree.body) is And:
            return Or(strip_negation(Not(tree.body.left)), strip_negation(Not(tree.body.right)))

        if type(tree.body) is Or:
            return And(strip_negation(Not(tree.body.left)), strip_negation(Not(tree.body.right)))

        # Universal and Existential switch
        if type(tree.body) is Universal:
            return Existential(tree.body.variable, strip_negation(Not(tree.body.body)))

        if type(tree.body) is Existential:
            return Universal(tree.body.variable, strip_negation(Not(tree.body.body)))

    return tree

# Move all quantifiers as far out as possible, creating a skolemizing map
def strip_quantifiers(tree):
    if type(tree) is Universal:
        skmap, subtree = strip_quantifiers(tree.body)
        for key in skmap:
            skmap[key].append(tree.variable)
        return skmap, subtree

    elif type(tree) is Existential:
        skmap, subtree = strip_quantifiers(tree.body)
        skmap[tree.variable] = []
        return skmap, subtree

    elif type(tree) is int:
        return {}, tree

    else:
        results = list(strip_quantifiers(x) for x in tree)

        # Compile Skolem map
        skmap = dict(i for result in results for i in result[0].items())

        # Compile tree
        subtree = type(tree)(*(x[1] for x in results))

        return skmap, subtree

# CNF a tree of Ands, Ors, and Nots
def cnf_stripped(tree):
    if type(tree) is Or:
        # Expand Ors by Cartesian product
        return set((l | r) for l in cnf(tree.left) for r in cnf(tree.right))

    elif type(tree) is And:
        # Expand Ands by union
        return cnf(tree.left) | cnf(tree.right)

    else:
        return {frozenset({tree})}

def cnf(tree):
    # Get Skolem map and stripped tree
    skmap, tree = strip_quantifiers(strip_negation(strip_inference(tree)))

    # Create Skolem functors
    substitution = {
            var:
                Functor(newconst(variables[var]), tuple(skmap[var]))
                if len(skmap[var]) > 0
                else newconst(variables[var])
            for var in skmap
    }

    # Perform substitution
    tree = substitute(tree, substitution)

    # CNF
    return cnf_stripped(tree)

def render_cnf(cnf_expression):
    if len(cnf_expression) == 1:
        disjunction = next(iter(cnf_expression))
        if len(disjunction) == 0:
            return '=><='
        else:
            return ' \u2228 '.join(render_tree(x) for x in disjunction)
    else:
        return ' \u2227 '.join('(%s)' % (' \u2228 '.join(render_tree(x) for x in disjunction)) for disjunction in cnf_expression)

render_prefs = {}

def render_tree(tree):
    if type(tree) is int:
        if tree in constants:
            return constants[tree]
        elif tree in variables:
            return variables[tree]

    elif type(tree) is Or:
        return '[%s] \u2228 [%s]' % (render_tree(tree.left), render_tree(tree.right))

    elif type(tree) is And:
        return '[%s] \u2227 [%s]' % (render_tree(tree.left), render_tree(tree.right))

    elif type(tree) is Implies:
        return '[%s] \u21D2 %s' % (render_tree(tree.left), render_tree(tree.right))

    elif type(tree) is Iff:
        return '[%s] \u21D4 %s' % (render_tree(tree.left), render_tree(tree.right))

    elif type(tree) is Not:
        return '\u00AC[%s]' % (render_tree(tree.body),)

    elif type(tree) is Universal:
        return '\u2200%s. %s' % (render_tree(tree.variable), render_tree(tree.body))

    elif type(tree) is Existential:
        return '\u2203%s. %s' % (render_tree(tree.variable), render_tree(tree.body))

    elif type(tree) is Relation:
        if tree.relation in render_prefs and render_prefs[tree.relation] == 'infix':
            return '[%s %s %s]' % (render_tree(tree.arguments[0]), render_tree(tree.relation), render_tree(tree.arguments[1]))
        elif tree.relation in render_prefs and render_prefs[tree.relation] == 'postfix':
            if len(tree.arguments) == 1:
                return '[%s %s]' % (render_tree(tree.arguments[0]), render_tree(tree.relation))
            else:
                return '[%s]%s' % (','.join(render_tree(x) for x in tree.arguments), render_tree(tree.relation))
        else:
            return '%s[%s]' % (render_tree(tree.relation), ', '.join(render_tree(x) for x in tree.arguments))

    elif type(tree) is Functor:
        if tree.functor in render_prefs and render_prefs[tree.functor] == 'infix':
            return '(%s %s %s)' % (render_tree(tree.arguments[0]), render_tree(tree.functor), render_tree(tree.arguments[1]))
        elif tree.functor in render_prefs and render_prefs[tree.functor] == 'postfix':
            if len(tree.arguments) == 1:
                return '(%s %s)' % (render_tree(tree.arguments[0]), render_tree(tree.functor))
            else:
                return '(%s)%s' % (','.join(render_tree(x) for x in tree.arguments), render_tree(tree.functor))
        else:
            return '%s(%s)' % (render_tree(tree.functor), ', '.join(render_tree(x) for x in tree.arguments))

if __name__ == '__main__':
    a = newvar()
    b = newvar()

    eq = 0

    tree = Universal(a, Existential(b, Iff(Relation(eq, Args(a, b)), Relation(eq, Args(b, a)))))
    print(render_tree(tree))
    print(render_tree(strip_inference(tree)))
    print(render_tree(strip_negation(strip_inference(tree))))
    skmap, tree = strip_quantifiers(strip_negation(strip_inference(tree)))

    # Create Skolem functors
    substitution = {var: Functor(newconst(variables[var]), tuple(skmap[var])) for var in skmap}

    # Perform substitution
    utree = substitute(tree, substitution)
    print(render_tree(utree))
    print(render_cnf(cnf(tree)))
