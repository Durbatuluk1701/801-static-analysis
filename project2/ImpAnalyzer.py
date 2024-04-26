import sys
from IMP.imp import create_ast
from IMP.imp_ast import *
import subprocess

PREAMBLE = """
(declare-datatypes (T1 T2) ((Pair (mk-pair (first T1) (second T2)))))

(declare-fun EN (Lines (Pair Vars Lines)) Bool)
(declare-fun EX (Lines (Pair Vars Lines)) Bool)

(define-fun ASGN ((v Vars) (l Lines)) Bool
; ASGN v l -> (forall v' l'; v <> v' -> (EN l (v', l') = EX l (v', l')))
; ASGN v l -> (forall l'; l = l' <-> EX l (v, l'))
  (forall ((l_3 Lines)) 
    (iff (= l l_3) (EX l (mk-pair v l_3)))
  )
)

(assert
  (forall ((l_1 Lines) (v Vars))
    (or
      (ASGN v l_1)
      (forall ((l_2 Lines)) (= (EN l_1 (mk-pair v l_2)) (EX l_1 (mk-pair v l_2))))
    )
  )
)

(define-fun NOT_ASGN ((l Lines)) Bool
; NOT_ASGN l -> (forall v2 l2, EN l (v2,l2) = EX l (v2,l2))
  (forall ((v Vars)) (not (ASGN v l)))
)

(declare-fun Flows (Lines Lines) Bool)
(assert
  (forall ((l_1 Lines) (l_2 Lines))
    (implies
      (Flows l_1 l_2)
      (forall ((val (Pair Vars Lines)))
        (implies
          (EX l_1 val)
          (EN l_2 val)
        )
      )
    )
  )
)

; Flowchains describes what it means to chain multiple flows assertions together
; e.g. if l1 flows to l2 and l2 flows to l3, then l1 flowchains to l3
; this allows us to make a restriction that if a line claims to have access to a variable from a different line,
; then that other line must flowchain and have an assignment
; e.g. if l3 claims to have access to v from l1, then it must be that l1 flowchains to l3 and l1 assigns v
; note/todo: it is possible this analysis is currently technically too broad,
; because it technically still allows Z3 to say l3 has v from l1 even if l2 comes between them and also assigns v
; however, it is also possible that other assertions made elsewhere make this impossible
; realistically, this is only being used to prevent Z3 from making an arbitrary assignment in a loop, which can be self-fulfilling due to flows analysis
(declare-fun Flowchains (Lines Lines) Bool)
; Flows -> Flowchains
(assert
  (forall ((l_1 Lines) (l_2 Lines))
    (=> (Flows l_1 l_2) (Flowchains l_1 l_2))
  )
)
; Flowchains l1 l2 /\ Flowchains l2 l3 <-> Flowchains l1 l3
(assert
  (forall ((l_1 Lines) (l_2 Lines) (l_3 Lines))
    (= (and (Flowchains l_1 l_2) (Flowchains l_2 l_3)) (Flowchains l_1 l_3))
  )
)
; l1 entry has v from l2 -> ASGN v l2 /\ Flowchains l2 l1
; not <->, because l2 may assign a var and chain into l1, but a distinct l3 may overwrite the assignment
(assert
  (forall ((l_1 Lines) (v Vars) (l_2 Lines))
    (=> (EN l_1 (mk-pair v l_2)) (and (ASGN v l_2) (Flowchains l_2 l_1)))
  )
)

; EN l1 has val <-> exists l2 where EX l2 val /\ flows l2 l1
; this is a distinct statement from the above Flowchains assertions, and should prevent the case
; where l3 has access to v from l1 even though l2 should be an overwriting assignment for v before l3
(assert
  (forall ((l_1 Lines) (val (Pair Vars Lines)))
    (=
      (and (not (= l_1 l?)) (EN l_1 val))
      (exists ((l_2 Lines)) (and (EX l_2 val) (Flows l_2 l_1)))
    ) 
  )
)

; if EX l != EN l for v then ASGN v l
(assert
  (forall ((l_1 Lines) (v Vars))
    (implies ;iff doesn't make sense (e.g. l?)
      (forall ((l_2 Lines)) (not (= (EX l_1 (mk-pair v l_2)) (EN l_1 (mk-pair v l_2)))))
      (ASGN v l_1)
    )
  )
)

;;;;;;;;;; l? Specific Information ;;;;;;;;;;
(assert (forall ((v Vars)) (ASGN v l?)))
(assert (forall ((v Vars) (l Lines)) (= (= l l?) (EN l? (mk-pair v l)))))
(assert (forall ((v Vars) (l Lines)) (= (= l l?) (EX l? (mk-pair v l)))))

(check-sat)"""


def generate_model(
    ast: Statement, start_line: int, cur_model: dict[int, str]
) -> tuple[int, dict[int, str]]:
    """
    Returns the next safe line to work on,
      the current working model

      NOTE: Always assumed that EXIT is last line
      so the first element of the tuple
    """
    ret_model = cur_model
    ret_end_line = start_line
    if isinstance(ast, Sequence):
        end_line_l, model_l = generate_model(ast.first, start_line, cur_model)
        # Button up the flows from EXIT_L to ENTRY_R
        ret_model[
            end_line_l - 1
        ] += f"\n(assert (forall ((l Lines)) (iff (= l l{end_line_l}) (Flows l{end_line_l - 1} l))))"
        ## Processing right side now
        ret_end_line, ret_model = generate_model(ast.second, end_line_l, model_l)
    elif isinstance(ast, Ite):
        # This line itself is a NOT_ASGN
        ret_model[start_line] = f"(assert (NOT_ASGN l{start_line}))"
        end_line_true, ret_model = generate_model(
            ast.true_stmt, start_line + 1, ret_model
        )
        # Adding flows from IF COND into TRUE and FALSE lines
        ret_model[
            start_line
        ] += f"(assert (forall ((l Lines)) (iff (or (= l l{start_line + 1}) (= l l{end_line_true})) (Flows l{start_line} l))))"
        ## Processing right side now
        ret_end_line, ret_model = generate_model(
            ast.false_stmt, end_line_true, ret_model
        )
        ## Adding magic skip at end
        ret_model[ret_end_line] = f"(assert (NOT_ASGN l{ret_end_line}))"
        ret_end_line += 1
        # Button up the flows from EXIT_TRUE to MAGIC SKIP
        ret_model[
            end_line_true - 1
        ] += f"\n(assert (forall ((l Lines)) (iff (= l l{ret_end_line}) (Flows l{end_line_true - 1} l))))"
        # Button up the flows from EXIT_FALSE to MAGIC SKIP
        ret_model[
            ret_end_line - 1
        ] += f"\n(assert (forall ((l Lines)) (iff (= l l{ret_end_line}) (Flows l{ret_end_line - 1} l))))"
    elif isinstance(ast, While):
        # This line itself is a NOT_ASGN
        ret_model[start_line] = f"(assert (NOT_ASGN l{start_line}))"
        # Now do the processing on the body
        (ret_end_line, ret_model) = generate_model(ast.body, start_line + 1, ret_model)
        # The start_line can flow into the loop, or past the end
        ret_model[
            start_line
        ] += f"\n(assert (forall ((l Lines)) (iff (or (= l l{start_line + 1}) (= l l{ret_end_line})) (Flows l{start_line} l))))"
        ## The EXIT of while should flow into the start of the loop,
        ## or past the end
        ret_model[
            ret_end_line - 1
        ] += f"\n(assert (forall ((l Lines)) (iff (or (= l l{start_line}) (= l l{ret_end_line})) (Flows l{ret_end_line - 1} l))))"
        # TODO: (assert (forall ((l Lines)) (iff (or (= l BEFORE_START) (= l END_BODY)) (Flows l START))))
        ## Adding magic skip at end
        ret_model[ret_end_line] = f"(assert (NOT_ASGN l{ret_end_line}))"
        ret_end_line += 1
    elif isinstance(ast, Assignment):
        # Then this line (the most recent line) is an assignment
        ret_model[start_line] = (
            f"(assert (forall ((v Vars)) (= (= v {ast.name}) (ASGN v l{start_line}))))"
        )
        ret_end_line = start_line + 1
    elif isinstance(ast, Skip):
        # This line itself is a NOT_ASGN
        ret_model[start_line] = f"(assert (NOT_ASGN l{start_line}))"
        ret_end_line += 1
        pass
    else:
        raise Exception(f"Unknown statement type: {ast}")

    return ret_end_line, ret_model


def get_all_vars_aexp(ast: Aexp) -> set[str]:
    if isinstance(ast, IntAexp):
        return set()
    elif isinstance(ast, VarAexp):
        return set([ast.name])
    elif isinstance(ast, BinopAexp):
        ret_set = get_all_vars_aexp(ast.left)
        return ret_set.union(get_all_vars_aexp(ast.right))
    else:
        raise Exception(f"Unknown aexp type: {ast}")


def get_all_vars_bexp(ast: Bexp) -> set[str]:
    if isinstance(ast, AndBexp):
        ret_set = get_all_vars_bexp(ast.left)
        return ret_set.union(get_all_vars_bexp(ast.right))
    elif isinstance(ast, OrBexp):
        ret_set = get_all_vars_bexp(ast.left)
        return ret_set.union(get_all_vars_bexp(ast.right))
    elif isinstance(ast, NotBexp):
        return get_all_vars_bexp(ast.exp)
    elif isinstance(ast, RelopBexp):
        ret_set = get_all_vars_aexp(ast.left)
        return ret_set.union(get_all_vars_aexp(ast.right))
    else:
        raise Exception(f"Unknown bexp type: {ast}")


def get_all_vars(ast: Statement) -> set[str]:
    if isinstance(ast, Sequence):
        ret_set = get_all_vars(ast.first)
        return ret_set.union(get_all_vars(ast.second))
    elif isinstance(ast, Ite):
        ret_set = get_all_vars_bexp(ast.condition)
        ret_set = ret_set.union(get_all_vars(ast.true_stmt))
        return ret_set.union(get_all_vars(ast.false_stmt))
    elif isinstance(ast, While):
        ret_set = get_all_vars_bexp(ast.condition)
        return ret_set.union(get_all_vars(ast.body))
    elif isinstance(ast, Assignment):
        ret_set = set([ast.name])
        return ret_set.union(get_all_vars_aexp(ast.aexp))
    elif isinstance(ast, Skip):
        return set()
    else:
        raise Exception(f"Unknown statement type: {ast}")


def generate_model_top(ast: Statement) -> str:
    preamble = PREAMBLE
    vars = get_all_vars(ast)
    last_line, model = generate_model(ast, 1, {})
    var_decl = f"(declare-datatypes () ((Vars {' '.join(vars)})))"
    lines_decl = (
        f"(declare-datatypes () ((Lines l? "
        + " ".join([f"l{i}" for i in range(1, last_line)])
        + ")))"
    )
    ret_val = (
        var_decl
        + "\n"
        + lines_decl
        + "\n"
        + preamble
        + "\n"
        + "(assert (forall ((l Lines)) (iff (= l l1) (Flows l? l))))\n"
        + "\n".join(model.values())
        + f"\n(assert (forall ((l Lines)) (not (Flows l{last_line - 1} l))))"
        + "\n(check-sat)\n(get-model)"
    )

    return ret_val


def main():
    if len(sys.argv) != 3:
        print(f"Usage: python {sys.argv[0]} <in_file_path> <out_file_path>")
        sys.exit(1)

    in_file_path = sys.argv[1]
    out_file_path = sys.argv[2]

    ast = create_ast(in_file_path)
    # print(ast.to_str(0))
    with open(out_file_path, "w") as fd:
        fd.write(generate_model_top(ast))
    subprocess.run(["z3", out_file_path])
    print("Done")


if __name__ == "__main__":
    main()
