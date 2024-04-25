# imp.py
# ------
#
# 1. Reads target program from command line
# 2. Tokenizes target program.
# 3. Builds a parser based on tokens.
# 4. Builds AST based on Parser
""" WE STOP HERE """
# 5. Stores final state of all assigned variables
# 6. Prints out each variable and final state

import sys

from IMP.imp_lexer import imp_lex
from IMP.imp_parser import imp_parse

def create_ast(filename):
    # Read target program
    text = open(filename).read()
    # Tokenize program
    tokens = imp_lex(text)
    # Attempt to consume tokens and build parse tree
    parse_result = imp_parse(tokens)
    if not parse_result:
        sys.stderr.write('Parse error!\n')
        sys.exit(1)
    # Build AST from parsed result to determine how to run target program
    ast = parse_result.value
    return ast
    """ BEYOND THIS POINT IS NO LONGER STATIC ANALYSIS """
    # print ast
    # # Store values of all variables to print out later
    # env = {}
    # ast.eval(env)
    #
    # sys.stdout.write('Final variable values:\n')
    # for name in env:
    #     sys.stdout.write('%s: %s\n' % (name, env[name]))