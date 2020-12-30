import system.io

def io.buffer_cmd (args : io.process.spawn_args) : io char_buffer :=
do child ← io.proc.spawn { args with stdout := io.process.stdio.piped },
  buf ← io.fs.read_to_end child.stdout,
  exitv ← io.proc.wait child,
  when (exitv ≠ 0) $ io.fail $ "process exited with status " ++ to_string exitv,
  return buf

def PYTHON_SCRIPT := "/cvxopt/opt.py"

meta def blah := do
  b <- tactic.unsafe_run_io $ io.buffer_cmd { cmd := "python3", args := [PYTHON_SCRIPT] },
  trace b.to_string
  return b.to_string


example : false :=
begin
-- blah,
end