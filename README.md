# CE-Lang - A Good Programming Language

A modern compiled systems programming language.

## Features

- **Fast Compilation**: Compiles to optimized C code
- **Native Execution**: Links with GCC for native binaries
- **Zero-copy VM**: Stack-based bytecode interpreter
- **Type Safety**: Static type system
- **Modern Syntax**: Clean, readable code

## Installation

### From Source

```bash
git clone https://github.com/ce-programming-language/ce.git celang
cd celang
make dev-setup
make build
sudo make install
```

## Quick Start

Create `main.ce`:

```ce
fn main() void {
  println("Hello, World!")
}
```

Run it:

```bash
ce run main.ce
```

## Usage

```
CE(1)                               Ce Manual                              CE(1)

NAME
     ce - Ce-lang - A Good Programming Language

SYNOPSIS
     ce [COMMAND] …

COMMANDS
     build [OPTION]… file
         Compile inserted ce-lang code file to binary executable

     debug [OPTION]… file
         Read ce-lang code file then show debug output

     lsp [OPTION]…
         Compile inserted ce-lang code file then execute that

     run [OPTION]… file
         Compile inserted ce-lang code file then execute that

COMMON OPTIONS
     --help[=FMT] (default=auto)
         Show this help in format FMT. The value FMT must be one of auto, pager,
         groff  or  plain.  With auto, the format is pager or plain whenever the
         TERM env var is dumb or undefined.

     --version
         Show version information.

EXIT STATUS
     ce exits with:

     0   on success.

     123
         on indiscriminate errors reported on standard error.

     124
         on command line parsing errors.

     125
         on unexpected internal errors (bugs).

Ce 0.1.0                                                                   CE(1)

```

## Examples

### Variables and Expressions

```ce
fn main() void {
  let x = 5
  println(x)
}
```

### Functions

```ce
fn add(a int, b int) int {
  return a + b
}
```

### Slices
```ce
import slices

fn main() !void {
  let mut x = slices.new<int>(0)
  
  x.append(1)
  x.append(3)
  x.append(8)

  println(x.get(0) catch (e) int { return 0 })
  println(x.get(1) catch (e) int { return 0 })
  println(x.get(2) catch (e) int { return 0 })
  println(x.get(3) catch (e) int { return 0 })
  println(x.get(4) catch (e) !int { raise e })
}

// output:
// 1
// 3
// 8
// 0
// Uncaught Error: unbound index
```

## Architecture

- **Lexer** (`lib/lexer/`) - Tokenization with Sedlex
- **Parser** (`lib/parser/`) - AST generation with Menhir
- **LLVM** (`lib/compiler`) - Bytecode compiler
- **CLI** (`bin/`) - Command-line interface

## Performance

- **Compilation**: Sub-100ms for typical files
- **Execution**: Near-native speed with LLVM optimization and Boehm GC
- **Memory**: < 1MB minimal runtime

## License

GPL-3.0 - See [LICENSE](./LICENSE) file

## Contributing

Contributions welcome! Please:
1. Fork the repository
2. Create a feature branch
3. Make your changes
4. Run `make fmt && make lint`
5. Submit a pull request

## Author

[hadihammurabi](https://github.com/hadihammurabi)
