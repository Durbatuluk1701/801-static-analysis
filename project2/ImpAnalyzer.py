import sys
from IMP.imp import create_ast
from IMP.imp_ast import Statement

if len(sys.argv) != 2:
    print(f"Usage: python {sys.argv[0]} <file_path>")
    sys.exit(1)

file_path = sys.argv[1]


def generate_model(ast: Statement):
    pass


ast = create_ast(file_path)
print(ast.to_str(0))
