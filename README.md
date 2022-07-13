# stack_vec  

Based on crate  [stack-vec](https://crates.io/crates/stack-vec).


Uses `std::mem::MaybeUninit<T>` to manage the underlying array `[std::mem::MaybeUninit<T>; SIZE]`.   
Create a `Vec<T>` like struct of a specific compile-time size on the stack.

The struct never allocates on the heap, and expose an API similar to `Vec<T>`.

## Install
Add the following line to your Cargo.toml file:
```toml
stack_vec = { git = "https://github.com/JikoUnderscore/stack_vec" , branch = "master"}
```

## Usage

``` rust
use stack_vec::StackVec;

fn main() {
    let mut sv = StackVec::<Rect2D, 24>::new();

    sv.push(Rect2D { x: 20, y: 30, w: 50, h: 50 });
    sv.push(Rect2D { x: 10, y: 50, w: 50, h: 50 });

    dbg!(&sv);
}

#[derive(Debug)]
struct Rect2D {
    x: u32,
    y: u32,
    w: u32,
    h: u32,
}
```



# License
MIT

