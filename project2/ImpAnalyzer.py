import sys
from IMP.imp import create_ast
from IMP.imp_ast import Statement, StatementType

if len(sys.argv) != 2:
    print(f"Usage: python {sys.argv[0]} <file_path>")
    sys.exit(1)

file_path = sys.argv[1]


def generate_model(ast: Statement):
    # Initialize model
    model = {}

    # Switch or match statement
    match ast.type():
        case StatementType.ASSIGN:
            pass
        case StatementType.ITE:
            pass
        case StatementType.WHILE:
            pass
        case StatementType.SKIP:
            pass
        case StatementType.SEQ:
            pass
        case _:
            raise Exception("Invalid statement type")

    return model


ast = create_ast(file_path)
print(ast.to_str(0))
