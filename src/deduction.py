import model
import heapq
import sys
sys.setrecursionlimit(5000)

DEBUG = False

def debug_print(*args):
    if DEBUG:
        print(*args)

def progress_log(*args):
    if DEBUG:
        print(*args)
    else:
        print(*args, end='\033[K\r', flush=True)

# Paramodulate with a specific source and target
def paramodulate_with(term, source, target):
    # If the source matches the entire term, we can replace.
    # We cannot paramodulate into an Args object.
    if (type(term) is not model.Args and
          type(term) is not model.Relation and type(target) is not model.Relation):
      mgu = model.mgu(term, source)

      if mgu is not None:
          debug_print('I can substitute', model.render_tree(term), model.render_tree(source), model.render_tree(target), mgu)
          yield target, mgu, (source, target)

    if type(term) is int:
        return

    # We can also match any subterm, and
    # replace only that subterm
    for subterm in term:
        #if ((type(term) is model.Functor and term is term.functor) or
        #        (type(term) is model.Relation and term is term.relation)):
        #    continue
        for submodulation, mgu, note in paramodulate_with(subterm, source, target):
            yield type(term)(*(submodulation if x is subterm else x for x in term)), mgu, note

def paramodulate(term_a, term_b):
    # Attempt paramodulations. 0 is the equality relation.
    if type(term_a) is model.Relation and term_a.relation == 0:
        yield from paramodulate_with(term_b, term_a.arguments[0], term_a.arguments[1])
        yield from paramodulate_with(term_b, term_a.arguments[1], term_a.arguments[0])

    if type(term_b) is model.Relation and term_b.relation == 0:
        yield from paramodulate_with(term_a, term_b.arguments[0], term_b.arguments[1])
        yield from paramodulate_with(term_a, term_b.arguments[1], term_b.arguments[0])

# Get all possible binary reductions as well as paramodulations
# of two disjunctions
def reductions(a, b):
    b = model.uniquify(b)

    for term_a in a:
        for term_b in b:
            # Attempt a binary reduction.
            if (type(term_a) is model.Not) != (type(term_b) is model.Not):
              # If only one is negated, figure out which one and continue
              neg_term = (term_a if type(term_a) is model.Not else term_b)
              pos_term = (term_b if type(term_a) is model.Not else term_a)

              avars = model.all_variables(neg_term)
              bvars = model.all_variables(pos_term)

              if len(set(avars) & set(bvars)) > 0:
                  print(model.render_tree(neg_term))
                  print(model.render_tree(pos_term))
                  raise 'ERROR!'

              # Get mgu
              mgu = model.mgu(neg_term.body, pos_term)

              # If they possibly match, yield the match
              if mgu is not None:
                  debug_print('yielding from binary reduction')
                  yield model.sub_all((a | b - {neg_term, pos_term}), mgu), ('reduction', pos_term)

            # Attempt paramodulations
            for paramodulated_term, mgu, note in paramodulate(term_a, term_b):
                yield model.sub_all(((a | b) - {term_a, term_b}) | {paramodulated_term}, mgu), ('paramodulation', (note[0], note[1], mgu))
        debug_print('done with some terms')
    debug_print('done with these disjunctions')

def find_contradiction(cnf, h, max_cost = 1000):
    debug_print(model.render_cnf(cnf))

    # Frontier -- the things not yet canonicalized
    # but which are true.
    frontier = []
    proof_map = {x: None for x in cnf}
    cost_map = {x: 0 for x in cnf}
    def push(x, a, b, note):
        if x not in cnf:
            debug_print('pushing', model.render_cnf({x}))
            if x in cost_map or x in proof_map:
                return
            cost_map[x] = h(x, a, b) + max(cost_map[a], cost_map[b]) + 1
            proof_map[x] = (a, b, note)
        heapq.heappush(frontier, (cost_map[x], x))

    pop = lambda: heapq.heappop(frontier)

    # The canon of deductions we have made so far
    canon = set()
    ordered_canon = []

    # The initial frontier contains all the axioms
    for axiom in cnf:
        push(model.canon(axiom), None, None, None)

    # Keep generating new deductions
    while frozenset() not in canon:
        cost, new_statement = pop()

        if cost > max_cost:
            return None

        if new_statement in canon:
            continue

        progress_log('[%s] [%s] %s' % (len(canon), cost, model.render_cnf({new_statement}),))
        canon.add(new_statement)
        ordered_canon.append(new_statement)

        for statement in ordered_canon:
            debug_print('reducing with next statement', model.render_cnf({statement}))
            for reduction, note in reductions(statement, new_statement):
                reduction = model.canon(reduction)
                push(reduction, statement, new_statement, note)

                # Return should happen from here
                if len(reduction) == 0:
                    debug_print('I AM DONE!')
                    return proof_map


    # Return the proof map
    return proof_map

def n_terms(term):
    r = 0

    if term in model.variables:
        r += 3
    elif term in model.constants:
        r += 1
    else:
        r += sum(n_terms(x) for x in term)

    if type(term) is model.Relation and term.relation not in model.constants:
        r += 20
    elif type(term) is model.Functor and term.functor not in model.constants:
        r += 20

    return r

def prove(axioms, statement, h = lambda x, a, b: n_terms(x) * 10):
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
        elif proof_map[x][2][0] == 'paramodulation':
            source, target, mgu = proof_map[x][2][1]
            lines.append('From [%d] and [%d] we can substitute %s = %s, giving us:' % (
                inv_index[proof_map[x][0]],
                inv_index[proof_map[x][1]],
                model.render_tree(model.substitute(source, mgu)),
                model.render_tree(model.substitute(target, mgu))
            ))
        elif proof_map[x][2][0] == 'reductoin':
            lines.append('From [%d] and [%d] we can apply the binary reduction of $s, giving us:' % (
                inv_index[proof_map[x][0]],
                inv_index[proof_map[x][1]],
                model.render_tree(proof_map[x][2][1])
            ))
        lines.append('  [%d] %s' % (i + 1, model.render_cnf({x})))

    return '\n'.join(lines)

if __name__ == '__main__':
    from model import Universal, Existential, And, Or, Implies, Iff, Not, Relation, Functor, Args, newvar, newconst, render_prefs

    eq = 0
    a = newvar('a')
    b = newvar('b')
    c = newvar('c')
    plus = newconst('+')
    times = newconst('*')
    zero = newconst('0')

    render_prefs[plus] = 'infix'
    render_prefs[times] = 'infix'
    render_prefs[eq] = 'infix'


    axioms = set.union(
        # Addition is commutative and associative
        model.cnf(Universal(a, Universal(b, Relation(eq, Args(Functor(plus, Args(a, b)), Functor(plus, Args(b, a))))))),
        model.cnf(Universal(a, Universal(b, Universal(c, Relation(eq, Args(
            Functor(plus, Args(a, Functor(plus, Args(b, c)))),
            Functor(plus, Args(Functor(plus, Args(a, b)), c))
        )))))),

        # Cancellation law for addition
        model.cnf(Universal(a, Universal(b, Universal(c, Implies(
          Relation(eq, Args(Functor(plus, Args(a, b)), Functor(plus, Args(a, c)))),
          Relation(eq, Args(b, c))
        ))))),

        # Multiplication is commutative and associative
        model.cnf(Universal(a, Universal(b, Relation(eq, Args(Functor(times, Args(a, b)), Functor(times, Args(b, a))))))),
        model.cnf(Universal(a, Universal(b, Universal(c, Relation(eq, Args(
            Functor(times, Args(a, Functor(times, Args(b, c)))),
            Functor(times, Args(Functor(times, Args(a, b)), c))
        )))))),

        # Multiplication distributes over addition
        model.cnf(Universal(a, Universal(b, Universal(c, Relation(eq, Args(
            Functor(times, Args(a, Functor(plus, Args(b, c)))),
            Functor(plus, Args(Functor(times, Args(a, b)), Functor(times, Args(a, c))))
        )))))),

        # Zero is the additive identity
        model.cnf(Universal(a, Relation(eq, Args(
            Functor(plus, Args(a, zero)),
            a
        )))),
    )

    x = newvar('x')

    '''
    proof_lines = [
        Universal(x, Universal(y, Universal(z,
            Relation(eq, Args(
                Functor(plus, Args(x, Functor(plus, Args(y, z)))),
                Functor(plus, Args(z, Functor(plus, Args(y, x))))
        ))))),
        Universal(x, Universal(y, Universal(z, Universal(w,
            Relation(eq, Args(
                Functor(plus, Args(Functor(plus, Args(x, y)), Functor(plus, Args(z, w)))),
                Functor(plus, Args(Functor(plus, Args(x, w)), Functor(plus, Args(z, y))))
        ))))))
    ]
    '''

    '''
    Approximation of the following proof:

    \\Theorem zeroprod (x)
      \\Conclusions
        \ x * 0 = 0
      \\Proof
        \ x * x = x * (x + 0)
        \ x * x = x * x + x * 0

        \ x * x = x * x + 0

        \ x * x + 0 = x * x + x * 0
        \ 0 = x * 0
        \\QED
    '''
    proof_lines = [
      #Universal(x, Relation(eq, Args(
      #  Functor(times, Args(x, x)),
      #  Functor(times, Args(x, Functor(plus, Args(x, zero))))
      #))),
      #Universal(x, Relation(eq, Args(Functor(times, Args(x, x)), Functor(plus, Args(Functor(times, Args(x, x)), Functor(times, Args(x, zero))))))),
      #Universal(x, Relation(eq, Args(Functor(times, Args(x, x)), Functor(plus, Args(Functor(times, Args(x, x)), zero))))),
      #Universal(x, Relation(eq, Args(Functor(plus, Args(Functor(times, Args(x, x)), zero)), Functor(plus, Args(Functor(times, Args(x, x)), Functor(times, Args(x, zero))))))),
      #Universal(x, Relation(eq, Args(zero, Functor(times, Args(x, zero))))),
      Universal(x, Relation(eq, Args(Functor(times, Args(x, zero)), zero)))
    ]

    for line in proof_lines:
        print('')
        print('We now demonstrate that %s' % (model.render_tree(line),))
        proof = prove(axioms, line)
        print('')
        print('Suppose for the sake of contradiction that %s' % (model.render_tree(Not(line)),))
        print('Then the following proof holds.')
        print(render_proof(proof))
        print('Thus we have reached a contradiction.')
        print('')

        axioms.update(set(model.canon(x) for x in model.cnf(line)))
