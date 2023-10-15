# rancor

rancor provides scalable and efficient error handling without using type
composition. This makes it best-suited for situations where:

- Programmatic error introspection is not useful
- Functions may error, but succeed most of the time
- Errors should provide as much useful detail as possible when emitted
- Use cases include both `no_std` and targets with support for `std`
