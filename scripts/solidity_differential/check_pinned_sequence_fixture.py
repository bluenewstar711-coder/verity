"""Self-check of the pinned-sequence instrument on a generic multi-entry-point fixture.

The fixture is committed into a fresh Git repository with a fixed author and
date, so its revision is reproducible. A positive campaign must agree across
A/B/C with both successes and reverts; the deliberate event-deletion model
mutant must diverge and shrink to a reproduced deletion-minimal witness.
"""
import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess

from .engine import HarnessError, write_json
from .pinned_sequence import campaign

FIXTURE = Path(__file__).resolve().parent / 'fixtures/pinned-sequence'
IDENTITY = {'GIT_AUTHOR_NAME': 'Fixture', 'GIT_AUTHOR_EMAIL': 'fixture@example.invalid',
            'GIT_COMMITTER_NAME': 'Fixture', 'GIT_COMMITTER_EMAIL': 'fixture@example.invalid',
            'GIT_AUTHOR_DATE': '2000-01-01T00:00:00Z', 'GIT_COMMITTER_DATE': '2000-01-01T00:00:00Z'}


def materialize(output):
    """Commit the fixture sources into `output/repository`; return its config path."""
    repository = output / 'repository'
    shutil.copytree(FIXTURE / 'src', repository / 'src')
    env = {**os.environ, **IDENTITY}

    def git(*args):
        return subprocess.run(['git', '-C', str(repository), *args], env=env, check=True,
                              capture_output=True, text=True).stdout.strip()

    git('init', '-q')
    git('add', 'src')
    git('-c', 'commit.gpgsign=false', 'commit', '-q', '-m', 'pinned-sequence fixture')
    config = json.loads((FIXTURE / 'config.json').read_text())
    config['revision'] = git('rev-parse', 'HEAD')
    path = output / 'config.json'
    write_json(path, config)
    return path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--transactions', type=int, default=64)
    parser.add_argument('--seed', type=int, default=2514)
    args = parser.parse_args()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    config = materialize(output)
    if campaign(config, output / 'positive', args.transactions, args.seed, 200) != 0:
        raise HarnessError('pinned-sequence positive campaign diverged')
    if campaign(config, output / 'drop-events', args.transactions, args.seed, 200,
                mutant='drop-events') != 1:
        raise HarnessError('pinned-sequence event-deletion mutant escaped detection')
    reduced = json.loads((output / 'drop-events/reduced.json').read_text())
    if not reduced['deletion_minimal'] or not reduced['transactions']:
        raise HarnessError('pinned-sequence mutant lacks a minimal reproduced witness')
    write_json(output / 'complete.json', {'exit': 0, 'transactions': args.transactions,
        'mutantWitness': len(reduced['transactions'])})
    print(f'pinned-sequence instrument: positive agrees, mutant detected: {output}')


if __name__ == '__main__':
    main()
