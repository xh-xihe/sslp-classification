"""Print read-only candidate roots; this command makes no review decisions."""
import argparse
from paper_correspondence_dossier import dossier

if __name__ == '__main__':
    import sys
    sys.stdout.reconfigure(encoding='utf8')
    p = argparse.ArgumentParser()
    p.add_argument('--source', default='supplementary')
    p.add_argument('--offset', type=int, default=0)
    p.add_argument('--limit', type=int, default=65)
    a = p.parse_args()
    for item in dossier('20261003', a.source, a.offset, a.limit)['claims']:
        roots = sorted({n for c in item['historical_candidates'] for n in c['lean_declarations']})
        print(item['claim']['id'], '@' + str(item['claim']['line']), ', '.join(roots))
