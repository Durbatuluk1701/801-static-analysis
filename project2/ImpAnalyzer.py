import sys
from IMP.imp import create_ast
from IMP.imp_ast import *

if len(sys.argv) != 2:
    print(f"Usage: python {sys.argv[0]} <file_path>")
    sys.exit(1)

file_path = sys.argv[1]


def generate_model(ast: Statement):
    # Initialize model
    model = {}

    # Switch or match statement
    if isinstance(ast, Sequence):
        model_l = generate_model(ast.first)
        model_r = generate_model(ast.second)
    elif isinstance(ast, Ite):
        pass
    elif isinstance(ast, While):
        pass
    elif isinstance(ast, Assignment):
        pass
    elif isinstance(ast, Skip):
        pass
    else:
        raise Exception(f"Unknown statement type: {ast}")

    return model


ast = create_ast(file_path)
print(ast.to_str(0))
