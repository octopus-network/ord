FROM docker.io/library/rust:1.75.0 as builder

WORKDIR /usr/src/ord

COPY . .

RUN cargo build --bin ord --release

FROM docker.io/library/rust:1.75.0

COPY --from=builder /usr/src/ord/target/release/ord /usr/local/bin

ENV RUST_BACKTRACE=1
ENV RUST_LOG=info