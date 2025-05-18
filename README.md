# OneBit algorithm in Rocq

This repo contains OneBit algorithm from Chapter 4 from [A Science of Concurrent Programming](https://lamport.azurewebsites.net/tla/science.pdf) formalized in rocq. It uses [coq-tla](https://github.com/tchajed/coq-tla/) library as underlying TLA embedding in rocq.

## Building

Supported Coq version: 8.18.0.

```
git submodule update --init --recursive
make
```

## Status

Safety property (`safety_theorem`) is formalizaed. Liveness property is work-in-progress.