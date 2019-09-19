"""
Toma como argumento el directorio donde estan los modelos
"""
from testing.shell_non_blocking import ShellProc

cores = 5
procs = []
try:
    import os
    files = [os.path.join(dp, f) for dp, dn, fn in os.walk("testing") for f in fn]
    for i,f in enumerate(files):
        if f.endswith(".model") and not os.path.exists(f.replace(".model",".hvm")):
            print("%s%%" % (i / len(files)))
            while len(procs) >= cores:
                procs = [p for p in procs if p.is_running()]
            procs.append(ShellProc('python3 test_minion_vs_hit_multiple_times.py "%s" > "%s"' % (f,f.replace(".model",".hvm"))))
            
except KeyboardInterrupt:
    pass
    
