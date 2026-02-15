#!/bin/bash

# 長い PATH `trace: .> LEAN_PATH=...`
lake build | sed 's/^trace: .> LEAN_PATH=.*$/trace: .> LEAN_PATH=.../' > __build.log
