# combinators.py
# --------------
# Language agnostic combinator library
#
# Combinators are one way to write a parser. A parser is essentially
# a function. It accepts a stream of tokens as an input. If it is
# successful, the parser will consume some tokens from the stream.
# It returns part of the final AST, along with the remaining tokens.
# A combinator is a function which produces a parser as its output,
# usually after taking one or more parsers as an input, hence the name
# "combinator". We can use a combinator to create a complete parser
# for a language like IMP by creating lots of smaller parsers for
# parts of the language, then using combinators to build the final
# parser.

# Parser combinators are usually fairly generic, and can be used with
# any language. First, we will write a language agnostic library of
# combinators, then use that to write our IMP parser.

class Result:
    def __init__(self, value, pos):
        self.value = value
        self.pos = pos

    def __repr__(self):
        return 'Result(%s, %d)' % (self.value, self.pos)

# Parsers are functions which take a stream of tokens as input.
# We will define parsers as objects with a __call__ method. This
# means that a parser object will behave as if it were a function,
# but we can also provide additional functionality by defining
# some operators.

# The __call__ method does the parsing. It's input is a full list
# of tokens, which are returned by the lexer, and an index into the
# list indicating the next token. The default implementation will
# always return `None` (failure), and the subclasses of `Parser` will
# provide their own __call__ implementation.

# The other methods: __add__, __mul__, __or__, __xor__ define the
# `+`, `*`, `|`, `^` operators. Each operator provides a shortcut
# for calling a different combinator.

class Parser:
    def __add__(self, other):
        return Concat(self, other)

    def __mul__(self, other):
        return Exp(self, other)

    def __or__(self, other):
        return Alternate(self, other)

    def __xor__(self, function):
        return Process(self, function)

# The next class we implement is the `Tag` combinator. It matches any
# token which has a particular tag. The value can be anything.
class Tag(Parser):
    def __init__(self, tag):
        self.tag = tag

    def __call__(self, tokens, pos):
        if pos < len(tokens) and tokens[pos][1] is self.tag:
            return Result(tokens[pos][0], pos + 1)
        else:
            return None

# The simplest combinator is `Reserved`, which will be used to parse
# reserved words and operators. It accepts tokens with a specific
# value and tag.

# NOTE: Tokens are nothing but value-tag pairs, where:
#       token[0] : value
#       token[1] : tag
class Reserved(Parser):
    def __init__(self, value, tag):
        self.value = value
        self.tag = tag

    def __call__(self, tokens, pos):
        if pos < len(tokens) and \
           tokens[pos][0] == self.value and \
           tokens[pos][1] is self.tag:
            return Result(tokens[pos][0], pos + 1)
        else:
            return None

# The `Tag` and `Reserved` combinators are our primitives. All combinators
# will be built out of them at the most basic level.

# In order to parse more complicated expressions, we can create an `concat`
# combinator which will take two parsers as input (left and right). When
# the concat parser is applied, it will apply the left parser, followed by
# the right parser. If both parsers are successful, the result value will
# be a pair containing the left and right results. If either parser is
# unsuccessful, `None` will be returned.
class Concat(Parser):
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def __call__(self, tokens, pos):
        left_result = self.left(tokens, pos)
        if left_result:
            right_result = self.right(tokens, left_result.pos)
            if right_result:
                combined_value = (left_result.value, right_result.value)
                return Result(combined_value, right_result.pos)
        return None

# The last combinator we need is an expression parser, which is used to match an
# expression which consists of a list of elements separated by something. Here is
# an example with compound statements:
#
#           a := 10;
#           b := 20;
#           c := 30
#
# In the above case, we have a list of statements separated by semicolons. In order
# to avoid a "left" recursive overflow, we will match a list similarly to the way
# `Rep` does. `Exp` takes two parsers as input. The first parser matches the actual
# elements of the list. The second matches the separators. On success, the separator
# parser must return a function which combines elements parsed on the left and right
# into a single value. The value is accumulated for the whole list, left -> right,
# and is returned.
class Exp(Parser):
    def __init__(self, parser, separator):
        self.parser = parser
        self.separator = separator

    def __call__(self, tokens, pos):
        result = self.parser(tokens, pos)

        def process_next(parsed):
            (sepfunc, right) = parsed
            return sepfunc(result.value, right)
        next_parser = self.separator + self.parser ^ process_next

        next_result = result
        while next_result:
            next_result = next_parser(tokens, result.pos)
            if next_result:
                result = next_result
        return result

# `Concat` is useful for parsing sequences of tokens. For example, to parse
# ` 1 + 2 `, we can write this as :
# parser = Concat(Concat(Tag(INT), Reserved('+', RESERVED)), Tag(Int))
# or using the + operator shorthand:
# parser = Tag(INT) + Reserved('+', RESERVED) + Tag(INT)

# The next combinator we build is the `Alternate` combinator. Like the `Concat`
# parser, it also takes a left and right parser as input. It starts by applying
# the left parser, and if successful that result is returned. If unsuccessful,
# it applies the right parser and returns its result.

# The `Alternate` class is useful for choosing among several possible parsers.
# For example, if we wanted to parse any binary operator:
#
#   parser = Reserved('+', RESERVED) |
#            Reserved('-', RESERVED) |
#            Reserved('*', RESERVED) |
#            Reserved('/', RESERVED)
class Alternate(Parser):
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def __call__(self, tokens, pos):
        left_result = self.left(tokens, pos)
        if left_result:
            return left_result
        else:
            right_result = self.right(tokens, pos)
            return right_result

# The `Opt` Parser is useful for optional text, such as the else-caluse of an
# if-statement. It takes one parser as input. If that parser is successful when
# applied, the result is returned normally. If it fails, a successful result is
# still returned, but the value of that result is `None`. No tokens are to be
# consumed in the failing case, the result position is the same as the initial
# position.
class Opt(Parser):
    def __init__(self, parser):
        self.parser = parser

    def __call__(self, tokens, pos):
        result = self.parser(tokens, pos)
        if result:
            return result
        else:
            return Result(None, pos)

# The `Rep` parser applies its input parser repeatedly until it fails. This is
# useful for generating lists of things. NOTE: `Rep` will successfully match an
# empty list and consume no tokens if its parser fails the first time it is
# applied.
class Rep(Parser):
    def __init__(self, parser):
        self.parser = parser

    def __call__(self, tokens, pos):
        results = []
        result = self.parser(tokens, pos)
        while result:
            results.append(result.value)
            pos = result.pos
            result = self.parser(tokens, pos)
        return Result(results, pos)

# The `Process` parser is a useful combinator which allows us to manipulate result
# values. Its input is a parser and a function. When the parser is applied successfully,
# the result value is passed to the function, and the return value from the function is
# returned instead of the original value. We will use `Process` to actually build the AST
# nodes out of the pairs and lists that `Concat` and `Rep` return.
class Process(Parser):
    def __init__(self, parser, function):
        self.parser = parser
        self.function = function

    def __call__(self, tokens, pos):
        result = self.parser(tokens, pos)
        if result:
            result.value = self.function(result.value)
            return result

# For example, consider the parser build with `Concat`. When it parsers `1 + 2`, the result
# value we actually get back is `(('1', '+'), '2'), which is not very useful. With `Process
# we can change that result. For example, the following parser would sum the parsed
# expression:
#
#               def process_func(parsed):
#                   ((1, _ ), r) = parsed
#                   return int(1) + int(r)
#
#               better_parser = parser ^ process_func


# The `Lazy` parser is a less useful combinator. Instead of taking an input parser,
# it takes a zero-argument function which returns a parser. `Lazy` will not call the
# function to get the parser until it is applied. This is useful to build recursive
# parsers (like how arithmetic expressions can include arithmetic expressions). Since
# the parser refers to itself, we can't just define it by referencing it directly;
# at the time the parser's defining expression is evaluated, the parser is not defined
# yet. We would not need this in a language with lazy evaluation like Haskell or Scala,
# but Python does not use lazy evaluation.
class Lazy(Parser):
    def __init__(self, parser_func):
        self.parser = None
        self.parser_func = parser_func

    def __call__(self, tokens, pos):
        if not self.parser:
            self.parser = self.parser_func()
        return self.parser(tokens, pos)

# Another combinator we will need to implement is the `Phrase`, which will take a
# single input parser, apply it and return its result normally. The only catch is
# that it will fail if its input parser does not consume all of the remaining tokens.
# The top level parser for IMP will be a `Phrase` parser. This prevents us from
# partially matching a program which has garbage at the end.
class Phrase(Parser):
    def __init__(self, parser):
        self.parser = parser

    def __call__(self, tokens, pos):
        result = self.parser(tokens, pos)
        if result and result.pos == len(tokens):
            return result
        else:
            return None