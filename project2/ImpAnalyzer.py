import sys
from IMP.imp import create_ast

if len(sys.argv) != 2:
    print(f"Usage: python {sys.argv[0]} <file_path>")
    sys.exit(1)

file_path = sys.argv[1]

ast = create_ast(file_path)
print(ast.to_str(0))
