# heapq

A minimal Rust library for heap-based priority queues. This crate provides
heap operations for efficient insertion, removal, and access to the smallest
element. It is inspired by Python's `heapq` module, but written
in safe, idiomatic Rust.

## Features

- Min-heap implementation
- Efficient push and pop operations
- Peek at the top element: `heap.get(0)`
- No unsafe code

## Implemented Functions
Each operation has three related functions. The first relies on the heap
item's type `T` for comparison operations; the second takes a `cmp` function
that accepts two items for comparison; and, the third takes `cmp` and additional
information `aux`, which gets passed to the `cmp` function when invoked.

- `heapify<T>(heap: &mut [T])`
    - `heapify_with<T, C>(heap: &mut [T], cmp: C)`
    - `heapify_with_aux<T, C, A>(heap: &mut [T], cmp: C, aux: A)`
- `heap_push<T>(heap: &mut Vec<T>, item: T)`
    - `heap_push_with<T, C>(heap: &mut Vec<T>, item: T, cmp: C)`
    - `heap_push_with_aux<T, C, A>(heap: &mut Vec<T>, item: T, cmp: C, aux: A)`
- `heap_pop<T>(heap: &mut Vec<T>) -> Option<T>`
    - `heap_pop_with<T, C>(heap: &mut Vec<T>, cmp: C) -> Option<T>`
    - `heap_pop_with_aux<T, C, A>(heap: &mut Vec<T>, cmp: C, aux: A) -> Option<T>`
- `heap_pushpop<T>(heap: &mut [T], item: T) -> T`
    - `heap_pushpop_with<T, C>(heap: &mut [T], item: T, cmp: C) -> T`
    - `heap_pushpop_with_aux<T, C, A>(heap: &mut [T], item: T, cmp: C, aux: A) -> T`
- `heap_replace<T>(heap: &mut [T], item: T) -> T`
    - `heap_replace_with<T, C>(heap: &mut [T], item: T, cmp: C) -> T`
    - `heap_replace_with_aux<T, C, A>(heap: &mut [T], item: T, cmp: C, aux: A) -> T`


## Usage

Add this to your `Cargo.toml`:

```
heapq = { git="https://github.com/ttappr/heapq.git" }
```

Import and use in your code:

```rust
use heapq::*;

let heap = &mut Vec::new();
heap_push(heap, 3);
heap_push(heap, 1);
heap_push(heap, 2);
assert_eq!(heap_pop(heap), Some(1));

let heap = &mut Vec::new();
let cmp = |a: &i32, b: &i32| a.cmp(b);

heap_push_with(heap, 3, cmp);
heap_push_with(heap, 1, cmp);
heap_push_with(heap, 2, cmp);
assert_eq!(heap_pop_with(heap, cmp), Some(1));

let values = [3, 1, 2];
let cmp = |a: &usize, b: &usize, x: &[i32]| x[*a].cmp(&x[*b]);

let index_heap = &mut Vec::new();

// Indexes for items in `values` are pushed onto the heap.
heap_push_with_aux(index_heap, 0, cmp, &values);
heap_push_with_aux(index_heap, 1, cmp, &values);
heap_push_with_aux(index_heap, 2, cmp, &values);

// Values popped from heap are indexes into `values`.
assert_eq!(heap_pop_with_aux(index_heap, cmp, &values), Some(1));
assert_eq!(heap_pop_with_aux(index_heap, cmp, &values), Some(2));
assert_eq!(heap_pop_with_aux(index_heap, cmp, &values), Some(0));
```

## Docs
Build the documentation using `cargo doc`. This should place the documentation
in the project folder under `./target/doc/heapq/index.html`.

## License

This project is licensed under the MIT License.
