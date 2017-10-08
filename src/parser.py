import model

def quantifier(tokens, lang, names):
    if tokens.peek() == 'forall' or tokens.peek() == 'exists':
        which = tokens.peek()

        tokens.take()

        var_name = tokens.take()
        var = model.newvar(var_name)
        names = names.register(var_name, var)

        tokens.take()
        body = quantifier(tokens)

        return (model.Universal if which == 'forall' else model.Existential)(var, body)

    else:
        return inference(tokens, lang, name)

def inference(tokens, lang, names):
    node = disjunction(tokens, lang, names)

    if tokens.peek() in ('=>', '<=>', 'implies', 'iff'):
        which = tokens.peek()
        tokens.take()

        node = (model.Implies if which in ('=>', 'implies') else model.Iff)(
            inference(tokens, lang, names)
        )

    return node

def disjunction(tokens, lang, names):
    node = conjunction(tokens, lang, names)

    if tokens.peek() == 'or':
        tokens.take()
        node = model.Or(node, disjunction(tokens, lang, names))

    return node

def conjunction(tokens, lang, names):
    node = negation(tokens, lang, names)

    if tokens.peek() == 'or':
        tokens.take()
        node = model.Or(node, conjunction(tokens, lang, names))

    return node

def negation(tokens, lang, names):
    if tokens.peek() == 'not':
        tokens.take()
        return model.Not(lor_primary(tokens, lang, names))
    else:
        return lor_primary(tokens, lang, names)

def lor_primary(tokens, lang, names):
    if tokens.peek() == '[':
        tokens.take()
        node = quantifier(tokens, lang, names)
        tokens.take()
        return node
    else:
        return term(tokens, lang, names)

def term(tokens, lang, names):
    return term_infix_relation(tokens, lang, names)

def term_infix_relation(tokens, lang, names, precedence = 0):
    if precedence >= len(lang.relation_infix_order):
        return term_functional_relation(tokens, lang, names)
    else:
        node = term_infix_relation(tokens, lang, names, precedence = precedence + 1)

        if tokens.peek() == lang.relation_infix_order[precedence]:
            operator = lang.relation_infix_order[precedence]
            constant = names.to_index(operator)

            return model.Relation(constant, model.Args(
                node,
                term_infix_relation(tokens, lang, names, precedence = precedence)
            ))

        return node

def term_functional_relation(tokens, lang, names):
    functor = value(tokens, lang, names)

    arguments = []
    if tokens.peek() == '[':
        tokens.take()
        while True:
            arguments.append(term(tokens, lang, names))
            if tokens.peek() != ',':
                break
        return model.Relation(functor, model.Args(*arguments))

    return functor

def value(tokens, lang, names):
    return value_infix(tokens, lang, names)

def value_infix(tokens, lang, names, precedence = 0)
    if precedence >= len(lang.functor_infix_order):
        return value_functional(tokens, lang, names)
    else:
        node = value_infix(tokens, lang, names, precedence = precedence + 1)

        if tokens.peek() == lang.functor_infix_order[precedence]:
            operator = lang.functor_infix_order[precedence]
            constant = names.to_index(operator)

            return model.Functor(constant, model.Args(
                node,
                value_infix(tokens, lang, names, precedence = precedence)
            ))

        return node

def value_functional(tokens, lang, names):
    functor = value_primary(tokens, lang, names)

    arguments = []
    if tokens.peek() == '(':
        tokens.take()
        while True:
            arguments.append(value(tokens, lang, names))
            if tokens.peek() != ',':
                break
        return model.Functor(functor, model.Args(*arguments))

    return functor

def value_primary(tokens, lang, names):
    if tokens.peek() == '(':
        tokens.take()
        node = value(tokens)
        tokens.take()
        return node
    else:
        return value_atomic(tokens)

def value_atomic(tokens, lang, names):
    return names.to_index(tokens.take())
