import model
import heapq

DEBUG = False #True

def debug_print(*args):
    if DEBUG:
        print(*args)

# Paramodulate with a specific source and target
def paramodulate_with(term, source, target):
    # If the source matches the entire term, we can replace.
    mgu = model.mgu(term, source)

    if mgu is not None:
        debug_print('I can substitute', model.render_tree(term), model.render_tree(source), model.render_tree(target))
        yield target, mgu

    if type(term) is int:
        return

    # We can also match any subterm, and
    # replace only that subterm
    for subterm in term:
        for submodulation, mgu in paramodulate_with(subterm, source, target):
            yield type(term)(*(submodulation if x is subterm else x for x in term)), mgu

def paramodulate(term_a, term_b):
    # Attempt paramodulations. 0 is the equality relation.
    if type(term_a) is model.Relation and term_a.relation == 0:
        yield from paramodulate_with(term_b, term_a.arguments[0], term_a.arguments[1])
        yield from paramodulate_with(term_b, term_a.arguments[1], term_a.arguments[0])

    if type(term_b) is model.Relation and term_b.relation == 0:
        yield from paramodulate_with(term_a, term_b.arguments[0], term_b.arguments[1])
        yield from paramodulate_with(term_a, term_b.arguments[1], term_b.arguments[0])

def reductions(a, b):
    b = model.uniquify(b)

    for term_a in a:
        for term_b in b:
            # Attempt paramodulations
            for paramodulated_term, mgu in paramodulate(term_a, term_b):
                debug_print('yielding from paramodulation')
                yield model.sub_all(((a | b) - {term_a, term_b}) | {paramodulated_term}, mgu)

            # Attempt a binary reduction.
            if (type(term_a) is model.Not) == (type(term_b) is model.Not):
                continue

            # If only one is negated, figure out which one and continue
            neg_term = (term_a if type(term_a) is model.Not else term_b)
            pos_term = (term_b if type(term_a) is model.Not else term_a)

            # Get mgu
            mgu = model.mgu(neg_term.body, pos_term)

            # If they possibly match, yield the match
            if mgu is not None:
                debug_print('yielding from binary reduction')
                yield model.sub_all((a | b - {neg_term, pos_term}), mgu)
        debug_print('done with some terms')
    debug_print('done with these disjunctions')

def find_contradiction(cnf, h, max_cost = 100):
    debug_print(model.render_cnf(cnf))

    # Frontier -- the things not yet canonicalized
    # but which are true.
    frontier = []
    proof_map = {x: None for x in cnf}
    cost_map = {x: 0 for x in cnf}
    def push(x, a, b):
        if x not in cnf:
            debug_print('pushing', model.render_cnf({x}))
            if x in cost_map or x in proof_map:
                return
            cost_map[x] = h(x, a, b) + max(cost_map[a], cost_map[b]) + 1
            proof_map[x] = (a, b)
        heapq.heappush(frontier, (cost_map[x], x))

    pop = lambda: heapq.heappop(frontier)

    # The canon of deductions we have made so far
    canon = set()

    # The initial frontier contains all the axioms
    for axiom in cnf:
        push(model.canon(axiom), None, None)

    # Keep generating new deductions
    while frozenset() not in canon:
        cost, new_statement = pop()

        if cost > max_cost:
            return None

        if new_statement in canon:
            continue

        debug_print('Adding this new statement:', model.render_cnf({new_statement}))
        canon.add(new_statement)

        for statement in canon:
            debug_print('reducing with next statement', model.render_cnf({statement}))
            for reduction in reductions(statement, new_statement):
                reduction = model.canon(reduction)
                push(reduction, statement, new_statement)

                # Return should happen from here
                if len(reduction) == 0:
                    debug_print('I AM DONE!')
                    return proof_map


    # Return the proof map
    return proof_map

def n_terms(term):
    if type(term) is int:
        return 1
    else:
        return sum(n_terms(x) for x in term)

def prove(axioms, statement, h = lambda x, a, b: n_terms(x)):
    # Assume statement is not true, and find a contradiction.
    return find_contradiction(axioms | model.cnf(model.Not(statement)), h)

def render_proof(proof_map):
    goal = frozenset()

    toposorted = []
    inv_index = {}

    lines = []

    def dfs(x):
        if x in inv_index:
            return
        if proof_map[x] is not None:
            dfs(proof_map[x][0])
            dfs(proof_map[x][1])
        toposorted.append(x)
        inv_index[x] = len(toposorted)

    dfs(goal)

    for i, x in enumerate(toposorted):
        if proof_map[x] is None:
            lines.append('The following is given:')
        else:
            lines.append('From [%d] and [%d] we have:' % (
                inv_index[proof_map[x][0]],
                inv_index[proof_map[x][1]]
            ))
        lines.append('  [%d] %s' % (i + 1, model.render_cnf({x})))

    return '\n'.join(lines)

if __name__ == '__main__':
    from model import Universal, Existential, And, Or, Implies, Iff, Not, Relation, Functor, Args, newvar, newconst

    eq = 0
    a = newvar('a')
    b = newvar('b')
    c = newvar('c')
    plus = newconst('+')

    axioms = set.union(
        model.cnf(Universal(a, Universal(b, Relation(eq, Args(Functor(plus, Args(a, b)), Functor(plus, Args(b, a))))))),
        model.cnf(Universal(a, Universal(b, Universal(c, Relation(eq, Args(
            Functor(plus, Args(a, Functor(plus, Args(b, c)))),
            Functor(plus, Args(Functor(plus, Args(a, b)), c))
        ))))))
    )

    x = newvar('x')
    y = newvar('y')
    z = newvar('z')

    desired = Universal(x, Universal(y, Universal(z,
        Relation(eq, Args(
            Functor(plus, Args(x, Functor(plus, Args(y, z)))),
            Functor(plus, Args(z, Functor(plus, Args(y, x))))
    )))))

    proof = prove(axioms, desired)

    print('Suppose for the sake of contradiction that %s' % (model.render_tree(Not(desired))))
    print('Then the following proof holds.')
    print(render_proof(proof))
    print('Thus we have reached a contradiction.')
