"""Optional local chunking helper. Load only checkpoints you created yourself."""
import argparse,json,pickle,time
from pathlib import Path
from three_level_replay import ThreeLevelRun
ap=argparse.ArgumentParser()
ap.add_argument('--checkpoint',required=True)
ap.add_argument('--steps',type=int,default=25000)
ap.add_argument('--seed',type=int,default=2026)
ap.add_argument('--output',required=True)
a=ap.parse_args();p=Path(a.checkpoint);start=time.monotonic()
if p.exists():
    with p.open('rb') as f: run,elapsed=pickle.load(f)
else:
    run=ThreeLevelRun(k=1,fanout=2,ell=3,t=18,seed=a.seed);elapsed=0
result=run.run(max_root_services=run.main_services+a.steps)
elapsed+=time.monotonic()-start
if 'paused_at_root_services' in result:
    with p.open('wb') as f:pickle.dump((run,elapsed),f,protocol=5)
    result['elapsed_seconds']=round(elapsed,3)
else:
    result.update(seed=a.seed,seconds=round(elapsed,3))
    Path(a.output).write_text(json.dumps(result,indent=2)+'\n')
    if p.exists():p.unlink()
print(json.dumps(result,indent=2))
