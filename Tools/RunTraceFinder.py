#!/usr/bin/python3.7

import sys
import glob
import os
import re
import shutil
import subprocess
import hashlib
import asyncio
import sys

from pathlib import Path
from multiprocessing import Process


if len(sys.argv) != 2:
    print("Incorrect number of arguments. use -h for more help.")
    sys.exit(0)

if sys.argv[1] == "-h" or sys.argv[1] == "--help":
    print("./RunExperiments [-h] [cnf_instances_directory]")
    sys.exit(0)

inputpath = sys.argv[1]

outputpath2 = './Traces/'
suffix = '.trace'
Path("./Traces").mkdir(parents=True, exist_ok=True)

MAX_PROCESSES = 7

# Structure is Outputpath2
async def process_csv(files, structure, dirpath, sem):
    async with sem:  
        print("The filename is: ", files)
        f = os.path.splitext(files)[0]
        path = structure + '/' + f + suffix
        #print("The Path is: ", path)
        Path(path).touch()
        file_dir = dirpath + '/' + files;
        with open(path, "w") as out:
            proc = await asyncio.create_subprocess_exec("qbfcert-1.0/depqbf/depqbf", "--trace", file_dir, stdout = out)
            await proc.wait()

async def main():
    sem = asyncio.Semaphore(MAX_PROCESSES)
    for dirpath, dirnames, filenames in os.walk(inputpath):
        structure = os.path.join(outputpath2, dirpath[len(inputpath):]) 
        print("The structure is: ", structure)
        await asyncio.gather(*[process_csv(files, structure, dirpath, sem) for files in filenames])

asyncio.run(main())
