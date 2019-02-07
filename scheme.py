"""This module implements the core Scheme interpreter functions, including the
eval/apply mutual recurrence, environment model, and read-eval-print loop.
"""

from scheme_primitives import *
from scheme_reader import *
from ucb import main, trace

##############
# Eval/Apply #
##############

def scheme_eval(expr, env):
    """Evaluate Scheme expression EXPR in environment ENV.

    >>> expr = read_line("(+ 2 2)")
    >>> expr
    Pair('+', Pair(2, Pair(2, nil)))
    >>> scheme_eval(expr, create_global_frame())
    4
    """
    if expr is None:
        raise SchemeError("Cannot evaluate an undefined expression.")

    # Evaluate Atoms
    if scheme_symbolp(expr):
        return env.lookup(expr)
    elif scheme_atomp(expr) or scheme_stringp(expr) or expr is okay:
        return expr

    # All non-atomic expressions are lists.
    if not scheme_listp(expr):
        raise SchemeError("malformed list: {0}".format(str(expr)))
    first, rest = expr.first, expr.second

    # Evaluate Combinations
    if (scheme_symbolp(first) # first might be unhashable
        and first in LOGIC_FORMS):
        return scheme_eval(LOGIC_FORMS[first](rest, env), env)
    elif first == "lambda":
        return do_lambda_form(rest, env)
    elif first == "mu":
        return do_mu_form(rest)
    elif first == "define":
        return do_define_form(rest, env)
    elif first == "quote":
        return do_quote_form(rest)
    elif first == "let":
        expr, env = do_let_form(rest, env)
        return scheme_eval(expr, env)
    else:
        procedure = scheme_eval(first, env)
        args = rest.map(lambda operand: scheme_eval(operand, env))
        return scheme_apply(procedure, args, env)


def scheme_apply(procedure, args, env):
    """Apply Scheme PROCEDURE to argument values ARGS in environment ENV."""
    if isinstance(procedure, PrimitiveProcedure):
        return apply_primitive(procedure, args, env)
    elif isinstance(procedure, LambdaProcedure):
        #begin problem 12
        new_frame = procedure.env.make_call_frame(procedure.formals, args)
        return scheme_eval(procedure.body, new_frame)
        #end problem 12
    elif isinstance(procedure, MuProcedure):
        #begin problem B17
        new_frame = env.make_call_frame(procedure.formals, args) #evaluated in parent frame (dynamic scoping)
        return scheme_eval(procedure.body, new_frame)
        #end problem B17
    else:
        raise SchemeError("Cannot call {0}".format(str(procedure)))

def apply_primitive(procedure, args, env):
    """Apply PrimitiveProcedure PROCEDURE to a Scheme list of ARGS in ENV.

    >>> env = create_global_frame()
    >>> plus = env.bindings["+"]
    >>> twos = Pair(2, Pair(2, nil))
    >>> apply_primitive(plus, twos, env)
    4
    """
    #begin problem 3
    #convert Scheme list of args to a Python list
    if len(args) == 0:
        _args = []
    else:
        _args = [args.first]
        i = 1 #index
        new_ele = args
        while i < len(args):
            new_ele = new_ele.second
            _args.append(new_ele.first)
            i += 1
    if procedure.use_env == True:
        _args.append(env)   #add current environment env as the last argument of args
    try:
        return procedure.fn(*_args) #Calling procedure.fn on the appropriate arguments
    except TypeError:
        raise SchemeError   #We want to raise a Scheme error if the function cannot be properly called
    #end problem 3

################
# Environments #
################

class Frame:
    """An environment frame binds Scheme symbols to Scheme values."""

    def __init__(self, parent):
        """An empty frame with a PARENT frame (that may be None)."""
        self.bindings = {}
        self.parent = parent

    def __repr__(self):
        if self.parent is None:
            return "<Global Frame>"
        else:
            s = sorted('{0}: {1}'.format(k,v) for k,v in self.bindings.items())
            return "<{{{0}}} -> {1}>".format(', '.join(s), repr(self.parent))

    def lookup(self, symbol):
        """Return the value bound to SYMBOL.  Errors if SYMBOL is not found."""
        #begin problem 4
        if symbol in self.bindings:
            return self.bindings[symbol]
        elif self.parent is not None:
            return Frame.lookup(self.parent, symbol)
        else:
        #end problem 4
            raise SchemeError("unknown identifier: {0}".format(str(symbol)))


    def global_frame(self):
        """The global environment at the root of the parent chain."""
        e = self
        while e.parent is not None:
            e = e.parent
        return e

    def make_call_frame(self, formals, vals):
        """Return a new local frame whose parent is SELF, in which the symbols
        in the Scheme formal parameter list FORMALS are bound to the Scheme
        values in the Scheme value list VALS. Raise an error if too many or too
        few arguments are given.

        >>> env = create_global_frame()
        >>> formals, vals = read_line("(a b c)"), read_line("(1 2 3)")
        >>> env.make_call_frame(formals, vals)
        <{a: 1, b: 2, c: 3} -> <Global Frame>>
        """
        frame = Frame(self)
        #begin problem 10
        if len(formals) != len(vals): #different number of formal parameters and arguments
            raise SchemeError('number of formal parameters and arguments differ')
        else:
            i = 0
            while i != len(vals):
                frame.define(formals.first, vals.first)
                formals = formals.second
                vals = vals.second
        #end problem 10
        return frame

    def define(self, sym, val):
        """Define Scheme symbol SYM to have value VAL in SELF."""
        self.bindings[sym] = val

class LambdaProcedure:
    """A procedure defined by a lambda expression or the complex define form."""

    def __init__(self, formals, body, env):
        """A procedure whose formal parameter list is FORMALS (a Scheme list),
        whose body is the single Scheme expression BODY, and whose parent
        environment is the Frame ENV.  A lambda expression containing multiple
        expressions, such as (lambda (x) (display x) (+ x 1)) can be handled by
        using (begin (display x) (+ x 1)) as the body."""
        self.formals = formals
        self.body = body
        self.env = env

    def __str__(self):
        return "(lambda {0} {1})".format(str(self.formals), str(self.body))

    def __repr__(self):
        args = (self.formals, self.body, self.env)
        return "LambdaProcedure({0}, {1}, {2})".format(*(repr(a) for a in args))

class MuProcedure:
    """A procedure defined by a mu expression, which has dynamic scope.
     _________________
    < Scheme is cool! >
     -----------------
            \   ^__^
             \  (oo)\_______
                (__)\       )\/\
                    ||----w |
                    ||     ||
    """

    def __init__(self, formals, body):
        """A procedure whose formal parameter list is FORMALS (a Scheme list),
        whose body is the single Scheme expression BODY.  A mu expression
        containing multiple expressions, such as (mu (x) (display x) (+ x 1))
        can be handled by using (begin (display x) (+ x 1)) as the body."""
        self.formals = formals
        self.body = body

    def __str__(self):
        return "(mu {0} {1})".format(str(self.formals), str(self.body))

    def __repr__(self):
        args = (self.formals, self.body)
        return "MuProcedure({0}, {1})".format(*(repr(a) for a in args))


#################
# Special forms #
#################

def do_lambda_form(vals, env):
    """Evaluate a lambda form with parameters VALS in environment ENV."""
    check_form(vals, 2)
    formals = vals[0]
    check_formals(formals)
    #begin problem 8
    #creates a LambdaProcedure instance by evaluating lambda expressions
    if len(vals) == 2: #cases with only one expression (length is 2 from formals + expr)
        return LambdaProcedure(formals, vals[1], env)
    else: #multiple expressions
        return LambdaProcedure(formals, Pair('begin', vals.second), env)
    #end problem 8

def do_mu_form(vals):
    """Evaluate a mu form with parameters VALS."""
    check_form(vals, 2)
    formals = vals[0]
    check_formals(formals)
    #begin problem B17
    #creates a MuProcedure instance (that is dynamically scoped) by evaluating mu expressions
    if len(vals) == 2: #cases with only one expression (length is 2 from formals + expr)
        return MuProcedure(formals, vals[1])
    else: #multiple expressions
        return MuProcedure(formals, Pair('begin', vals.second))
    #end problem B17

def do_define_form(vals, env):
    """Evaluate a define form with parameters VALS in environment ENV."""
    check_form(vals, 2)
    #target = vals[0]   #original given code: seems to produce an error by treating vals
                        #as a Python list when it's a Scheme list/expression, i.e., nested pairs
                        #(everything after the "define" is passed here as vals)
    target = vals.first
    if scheme_symbolp(target):
        check_form(vals, 2, 2)
        #begin problem A5
        env.define(target, scheme_eval(vals.second.first, env))
        return target
        #end problem A5
    elif isinstance(target, Pair):
        #begin problem A9
        if not scheme_symbolp(target.first):
            raise SchemeError('invalid argument')
        #construct a lambda expression and evaluate it with do_lambda_form.
        expr = Pair(target.second, vals.second)
        #return target.first #Not needed
        env.define(target.first, do_lambda_form(expr, env)) #define the function at target.first
                                                            #in current env as a lambda form with formals
                                                            #from target.second and the rest of vals
                                                            #(vals.second) as the body of the lambda define
        #end problem A9
    else:
        raise SchemeError("bad argument to define")

def do_quote_form(vals):
    """Evaluate a quote form with parameters VALS."""
    check_form(vals, 1, 1)
    #begin problem B6
    return vals.first
    #end problem B6


def do_let_form(vals, env):
    """Evaluate a let form with parameters VALS in environment ENV."""
    check_form(vals, 2)
    bindings = vals[0]
    exprs = vals.second
    if not scheme_listp(bindings):
        raise SchemeError("bad bindings list in let form")

    # Add a frame containing bindings
    names, values = nil, nil
    #begin problem A16
    for binding in bindings:
        if len(binding) > 2:
            raise SchemeError('too many values in bindings')
        if not scheme_symbolp(binding[0]):
            raise SchemeError('binding is not a symbol')
        names = Pair(binding[0], names) #adding the names in order to itself
        values = Pair(scheme_eval(binding[1], env), values) #values are found by evaluating the corresponding pair.second
    #end problem A16
    new_env = env.make_call_frame(names, values)

    # Evaluate all but the last expression after bindings, and return the last
    last = len(exprs)-1
    for i in range(0, last):
        scheme_eval(exprs[i], new_env)
    return exprs[last], new_env


#########################
# Logical Special Forms #
#########################

def do_if_form(vals, env):
    """Evaluate if form with parameters VALS in environment ENV."""
    check_form(vals, 2, 3)
    #begin problem A13
    if scheme_true(vals[0]):
        return scheme_eval(vals[1], env)
    elif len(vals) == 2:
        return okay
    else:
        return scheme_eval(vals[2], env)
    #end problem A13

def do_and_form(vals, env):
    """Evaluate short-circuited and with parameters VALS in environment ENV."""
    #begin problem B14
    for exprs in vals:
        if scheme_false(exprs): return False
    if len(vals) == 0:
        return True
    else:
        return vals[len(vals) - 1]
    #end problem B14

def quote(value):
    """Return a Scheme expression quoting the Scheme VALUE.

    >>> s = quote('hello')
    >>> print(s)
    (quote hello)
    >>> scheme_eval(s, Frame(None))  # "hello" is undefined in this frame.
    'hello'
    """
    return Pair("quote", Pair(value, nil))

def do_or_form(vals, env):
    """Evaluate short-circuited or with parameters VALS in environment ENV."""
    #begin problem B14
    for exprs in vals:
        if scheme_true(exprs): return exprs
    return False
    #end problem B14

def do_cond_form(vals, env):
    """Evaluate cond form with parameters VALS in environment ENV."""
    num_clauses = len(vals)
    for i, clause in enumerate(vals):
        check_form(clause, 1)
        if clause.first == "else":
            if i < num_clauses-1:
                raise SchemeError("else must be last")
            test = True
            if clause.second is nil:
                raise SchemeError("badly formed else clause")
        else:
            test = scheme_eval(clause.first, env)
        if scheme_true(test):
            #begin problem A15
            if clause.second == nil: #no subexpression/empty body of cond expression
                return test
            if len(clause.second) > 1: #body of cond with multple expressions
                return do_begin_form(clause.second, env)
            return clause.second.first
            #end problem A15
    return okay
    
def do_begin_form(vals, env):
    """Evaluate begin form with parameters VALS in environment ENV."""
    check_form(vals, 1)
    #begin problem 7
    # new_ele = vals[0]
    # i = 1 #index
    # while i <= (len(vals) - 1):
        # scheme_eval(new_ele, env)
        # i += 1
        # new_ele = vals[i]
    for i in range(len(vals)-1): #Note: Should look into why for loop worked but while loop didn't
        scheme_eval(vals[i],env)
    return vals[len(vals)-1]
    #end problem 7

LOGIC_FORMS = {
        "and": do_and_form,
        "or": do_or_form,
        "if": do_if_form,
        "cond": do_cond_form,
        "begin": do_begin_form,
        }

# Utility methods for checking the structure of Scheme programs

def check_form(expr, min, max = None):
    """Check EXPR (default SELF.expr) is a proper list whose length is
    at least MIN and no more than MAX (default: no maximum). Raises
    a SchemeError if this is not the case."""
    if not scheme_listp(expr):
        raise SchemeError("badly formed expression: " + str(expr))
    length = len(expr)
    if length < min:
        raise SchemeError("too few operands in form")
    elif max is not None and length > max:
        raise SchemeError("too many operands in form")

def check_formals(formals):
    """Check that FORMALS is a valid parameter list, a Scheme list of symbols
    in which each symbol is distinct. Raise a SchemeError if the list of formals
    is not a well-formed list of symbols or if any symbol is repeated.

    >>> check_formals(read_line("(a b c)"))
    """
    #begin problem b11
    i = 0
    used_symbols = []
    while i != len(formals):
        if not scheme_symbolp(formals.first):
            raise SchemeError('list of formals is not a well-formed list of symbols')
        if formals.first in used_symbols:
            raise SchemeError('list of formals includes repeated values')
        used_symbols.append(formals.first)
        formals = formals.second
    #end problem b11

##################
# Tail Recursion #
##################

def scheme_optimized_eval(expr, env):
    """Evaluate Scheme expression EXPR in environment ENV."""
    while True:
        if expr is None:
            raise SchemeError("Cannot evaluate an undefined expression.")

        # Evaluate Atoms
        if scheme_symbolp(expr):
            return env.lookup(expr)
        elif scheme_atomp(expr) or scheme_stringp(expr) or expr is okay:
            return expr

        # All non-atomic expressions are lists.
        if not scheme_listp(expr):
            raise SchemeError("malformed list: {0}".format(str(expr)))
        first, rest = expr.first, expr.second

        # Evaluate Combinations
        if (scheme_symbolp(first) # first might be unhashable
            and first in LOGIC_FORMS):
            "*** YOUR CODE HERE ***"
        elif first == "lambda":
            return do_lambda_form(rest, env)
        elif first == "mu":
            return do_mu_form(rest)
        elif first == "define":
            return do_define_form(rest, env)
        elif first == "quote":
            return do_quote_form(rest)
        elif first == "let":
            "*** YOUR CODE HERE ***"
        else:
            "*** YOUR CODE HERE ***"

################################################################
# Uncomment the following line to apply tail call optimization #
################################################################
# scheme_eval = scheme_optimized_eval


################
# Input/Output #
################

def read_eval_print_loop(next_line, env, quiet=False, startup=False,
                         interactive=False, load_files=()):
    """Read and evaluate input until an end of file or keyboard interrupt."""
    if startup:
        for filename in load_files:
            scheme_load(filename, True, env)
    while True:
        try:
            src = next_line()
            while src.more_on_line:
                expression = scheme_read(src)
                result = scheme_eval(expression, env)
                if not quiet and result is not None:
                    print(result)
        except (SchemeError, SyntaxError, ValueError, RuntimeError) as err:
            if (isinstance(err, RuntimeError) and
                'maximum recursion depth exceeded' not in err.args[0]):
                raise
            print("Error:", err)
        except KeyboardInterrupt:  # <Control>-C
            if not startup:
                raise
            print("\nKeyboardInterrupt")
            if not interactive:
                return
        except EOFError:  # <Control>-D, etc.
            return


def scheme_load(*args):
    """Load a Scheme source file. ARGS should be of the form (SYM, ENV) or (SYM,
    QUIET, ENV). The file named SYM is loaded in environment ENV, with verbosity
    determined by QUIET (default true)."""
    if not (2 <= len(args) <= 3):
        vals = args[:-1]
        raise SchemeError("wrong number of arguments to load: {0}".format(vals))
    sym = args[0]
    quiet = args[1] if len(args) > 2 else True
    env = args[-1]
    if (scheme_stringp(sym)):
        sym = eval(sym)
    check_type(sym, scheme_symbolp, 0, "load")
    with scheme_open(sym) as infile:
        lines = infile.readlines()
    args = (lines, None) if quiet else (lines,)
    def next_line():
        return buffer_lines(*args)
    read_eval_print_loop(next_line, env.global_frame(), quiet=quiet)
    return okay

def scheme_open(filename):
    """If either FILENAME or FILENAME.scm is the name of a valid file,
    return a Python file opened to it. Otherwise, raise an error."""
    try:
        return open(filename)
    except IOError as exc:
        if filename.endswith('.scm'):
            raise SchemeError(str(exc))
    try:
        return open(filename + '.scm')
    except IOError as exc:
        raise SchemeError(str(exc))

def create_global_frame():
    """Initialize and return a single-frame environment with built-in names."""
    env = Frame(None)
    env.define("eval", PrimitiveProcedure(scheme_eval, True))
    env.define("apply", PrimitiveProcedure(scheme_apply, True))
    env.define("load", PrimitiveProcedure(scheme_load, True))
    add_primitives(env)
    return env

@main
def run(*argv):
    next_line = buffer_input
    interactive = True
    load_files = ()
    if argv:
        try:
            filename = argv[0]
            if filename == '-load':
                load_files = argv[1:]
            else:
                input_file = open(argv[0])
                lines = input_file.readlines()
                def next_line():
                    return buffer_lines(lines)
                interactive = False
        except IOError as err:
            print(err)
            sys.exit(1)
    read_eval_print_loop(next_line, create_global_frame(), startup=True,
                         interactive=interactive, load_files=load_files)
    tscheme_exitonclick()
