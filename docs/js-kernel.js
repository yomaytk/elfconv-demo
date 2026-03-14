var Module = (() => {
  return (async function (moduleArg = {}) {
    var moduleRtn;
    var Module = moduleArg;
    var readyPromiseResolve, readyPromiseReject;
    var readyPromise = new Promise((resolve, reject) => {
      readyPromiseResolve = resolve;
      readyPromiseReject = reject
    });
    var ENVIRONMENT_IS_WEB = typeof window == "object";
    var ENVIRONMENT_IS_WORKER = typeof WorkerGlobalScope != "undefined";
    var arguments_ = [];
    var initProcessJsPath = Module["initProgram"] ? Module["initProgram"].slice(0, -5) + ".js" : "process-worker.js";
    var quit_ = (status, toThrow) => {
      throw toThrow
    };
    var _scriptName = import.meta.url;
    var INITIAL_MEMORY_SIZE = 9192; // 128 MiB (1page: 64KiB => 2048 page: 128 MiB)
    var userBinList = Module["executables"];
    var jsKernelBootMs = 0;
    var CLK_TCK = 100;

    var initProcessInitialized = false;
    var initWasmDoneNum = 0;
    var tEcvPid = -1;  // used for multi processes FS.
    var ecvPidCounter = 42;
    var gWasmMemory;
    var SysFuncMap = new Map();
    var processes = new Map();
    var FIFO_AtomicBuf = new SharedArrayBuffer(4 * 4096); // FD: 0~4096

    const prLingOffset = 4;
    const childProcessMax = 20;

    // Linux macro
    const __FD_SETSIZE = 1024;
    const __KERNEL_FD_SETMAXID = 16;

    // Basic access modes (from asm-generic/fcntl.h)
    const O_RDONLY = 0x0;        // 0       : Open for read-only
    const O_WRONLY = 0x1;        // 1       : Open for write-only
    const O_RDWR = 0x2;        // 2       : Open for read/write

    // Open flags (from asm-generic/fcntl.h)
    const O_CREAT = 0o100;      // 64      : Create file if it does not exist
    const O_EXCL = 0o200;      // 128     : Error if O_CREAT and file exists
    const O_NOCTTY = 0o400;      // 256     : Do not assign controlling terminal
    const O_TRUNC = 0o1000;     // 512     : Truncate file to zero length
    const O_APPEND = 0o2000;     // 1024    : Append writes to end of file
    const O_NONBLOCK = 0o4000;     // 2048    : Non-blocking I/O
    const O_DSYNC = 0o10000;    // 4096    : Synchronized data-only writes
    const O_SYNC = 0o4010000;  // 1052672 : POSIX O_SYNC (data+metadata sync)

    // close-on-exec
    const O_CLOEXEC = 0o2000000;  // 524288  : Set FD_CLOEXEC on open
    const FD_CLOEXEC = 1; // close-on-exec bit on fd_flags.

    // Additional Linux open flags
    const O_DIRECTORY = 0o200000;   // 65536   : Fail if path is not a directory
    const O_NOFOLLOW = 0o400000;   // 131072  : Do not follow symbolic links

    // File type bits (st_mode) — from stat.h
    const S_IFMT = 0o170000;      // 61440   : Bit mask for file type
    const S_IFREG = 0o100000;      // 32768   : Regular file
    const S_IFDIR = 0o040000;      // 16384   : Directory
    const S_IFIFO = 0o010000;      // 4096    : FIFO / pipe
    const S_IFCHR = 0o020000;      // 8192    : Character device
    const S_IFBLK = 0o060000;      // 24576   : Block device
    const S_IFLNK = 0o120000;      // 40960   : Symbolic link

    // Permission bits (from <sys/stat.h>)
    // User (owner) permissions
    const S_IRWXU = 0o700;   // 448  : user  (owner) read, write, execute
    const S_IRUSR = 0o400;   // 256  : user  read
    const S_IWUSR = 0o200;   // 128  : user  write
    const S_IXUSR = 0o100;   // 64   : user  execute

    // Group permissions
    const S_IRWXG = 0o070;   // 56   : group read, write, execute
    const S_IRGRP = 0o040;   // 32   : group read
    const S_IWGRP = 0o020;   // 16   : group write
    const S_IXGRP = 0o010;   // 8    : group execute

    // Others permissions
    const S_IRWXO = 0o007;   // 7    : others read, write, execute
    const S_IROTH = 0o004;   // 4    : others read
    const S_IWOTH = 0o002;   // 2    : others write
    const S_IXOTH = 0o001;   // 1    : others execute

    // poll
    const POLLIN = 0x1;   // Data available to read
    const POLLOUT = 0x2;   // Writing will not block
    const POLLPRI = 0x4;   // Urgent data / high-priority data available
    const POLLERR = 0x8;   // Error condition on FD (always reported)
    const POLLHUP = 0x10;  // Hang up (peer closed / no writers)

    // Pipe
    const PIPE_MAX_SZ = 65536;

    function getNewEcvPid() {
      return ecvPidCounter++;
    }

    function growMemViews(wasmMemory_) {
      if (wasmMemory_.buffer != HEAP8.buffer) {
        updateMemoryViews(wasmMemory_);
      }
    }

    function updateMemoryViews(wasmMemory_) {
      var b = wasmMemory_.buffer;
      HEAP8 = new Int8Array(b);
      HEAP16 = new Int16Array(b);
      HEAPU8 = new Uint8Array(b);
      HEAPU16 = new Uint16Array(b);
      HEAP32 = new Int32Array(b);
      HEAPU32 = new Uint32Array(b);
      HEAPF32 = new Float32Array(b);
      HEAPF64 = new Float64Array(b);
      HEAP64 = new BigInt64Array(b);
      HEAPU64 = new BigUint64Array(b)
    }

    var readAsync, readBinary;
    if (ENVIRONMENT_IS_WEB || ENVIRONMENT_IS_WORKER) {
      try {
        const _ = new URL(".", _scriptName).href
      } catch { } {
        if (ENVIRONMENT_IS_WORKER) {
          readBinary = url => {
            var xhr = new XMLHttpRequest;
            xhr.open("GET", url, false);
            xhr.responseType = "arraybuffer";
            xhr.send(null);
            return new Uint8Array(xhr.response)
          }
        }
        readAsync = async url => {
          var response = await fetch(url, {
            credentials: "same-origin"
          });
          if (response.ok) {
            return response.arrayBuffer()
          }
          throw new Error(response.status + " : " + response.url)
        }
      }
    } else { }
    var out = console.log.bind(console);
    var err = console.error.bind(console);
    var ABORT = false;
    var EXITSTATUS;
    var HEAP8, HEAPU8, HEAP16, HEAPU16, HEAP32, HEAPU32, HEAPF32, HEAP64, HEAPU64, HEAPF64;

    var WORKER_MGR = {
      wasmModules: new Map(),
      workerInfoPool: [],
      prWorkerPoolCapacity: 20,
      dupWorkerNum: 3,
      S_STOP: 0,
      S_RUNNING: 1,
      newProcessMemory(memSizeMiB) { // Wasm initial memory size (INITIAL_MEMORY_SIZE): 128 MiB
        return new WebAssembly.Memory({
          initial: memSizeMiB,
          maximum: 18384,
          shared: true
        });
      },
      init(userBinSet) {
        for (let userBinPath of userBinSet) {
          // We create the 3 workers for the every executable binary.
          // When we try 4 or more workers, it will take a bit time to start the target program.
          for (let i = 0; i < this.dupWorkerNum; i++) {
            let jsPath = userBinPath + ".js";
            let wasmPath = userBinPath + ".wasm";
            let id = this.workerInfoPool.length;
            let memory = this.newProcessMemory(INITIAL_MEMORY_SIZE);
            let worker = new Worker(new URL(jsPath, import.meta.url), {
              type: "module",
              name: `${jsPath}-worker-${id}`,
            });
            let wasmModule = this.wasmModules.get(wasmPath);
            if (!wasmModule) {
              throw new Error(`wasm module '${wasmPath}' has not been initialzed yet (at WORKER_MGR.init).`);
            }
            this.setInitialMsgHandling(worker);
            this.workerInfoPool.push({
              id: id,
              status: this.S_STOP,
              jsPath: jsPath,
              memory: memory,
              worker: worker,
              module: wasmModule,
            });
            worker.postMessage({
              cmd: "initWasm",
              workerId: id,
              wasmProgram: wasmPath,
              wasmMemory: memory,
              wasmModule: wasmModule,
            });
          }
        }
      },
      getAvailableWorkerInfo(jsPath) {
        let workerInfo = null;
        // find the existing worker.
        for (let prWorker of this.workerInfoPool) {
          if (prWorker.jsPath === jsPath && prWorker.status === this.S_STOP) {
            prWorker.status = this.S_RUNNING;
            workerInfo = prWorker;
            break;
          }
        }
        // create the new worker.
        if (!workerInfo) {
          let id = this.workerInfoPool.length;
          let memory = this.newProcessMemory(INITIAL_MEMORY_SIZE);
          let wasmPath = jsPath.slice(0, -3) + ".wasm";
          let worker = new Worker(new URL(jsPath, import.meta.url), {
            type: "module",
            name: `${jsPath}-worker-${id}`,
          });
          let wasmModule = this.wasmModules.get(wasmPath);
          if (!wasmModule) {
            throw new Error(`wasm module '${wasmPath}' has not been initialized yet (at getAvailableWorkerInfo).`);
          }
          this.setInitialMsgHandling(worker);
          workerInfo = {
            id: id,
            status: this.S_RUNNING,
            jsPath: jsPath,
            memory: memory,
            worker: worker,
            module: wasmModule,
          };
          this.workerInfoPool.push(workerInfo);
          worker.postMessage({
            cmd: "initWasm",
            workerId: id,
            wasmProgram: wasmPath,
            wasmMemory: memory,
            wasmModule: wasmModule
          });
        }
        return workerInfo;
      },
      rebootWorker(workerId) {
        let oldWorkerInfo = this.workerInfoPool[workerId];
        let jsPath = oldWorkerInfo.jsPath;
        let wasmPath = jsPath.slice(0, -3) + ".wasm";
        let newMemory = this.newProcessMemory(INITIAL_MEMORY_SIZE);
        let newWorker = new Worker(new URL(jsPath, import.meta.url), {
          type: "module",
          name: `${jsPath}-worker-${workerId}`,
        });
        let wasmModule = oldWorkerInfo.module;
        this.setInitialMsgHandling(newWorker);
        this.workerInfoPool[workerId] = {
          id: oldWorkerInfo.id,
          status: this.S_STOP,
          jsPath: jsPath,
          memory: newMemory,
          worker: newWorker,
          module: wasmModule,
        };
        newWorker.postMessage({
          cmd: "initWasm",
          workerId: workerId,
          wasmProgram: wasmPath,
          wasmMemory: newMemory,
          wasmModule: wasmModule,
        })
      },
      setInitialMsgHandling(worker) {
        worker.onmessage = e => {
          let d = e["data"];

          tEcvPid = d.ecvPid;

          // run system call.
          if (d.cmd === "sysRun") {
            runSyscall(d);
          }
          // check whether PTY is ready or not
          else if (d.cmd === "PTY_ReadableCheck") {
            PTY_ReadableAtomicCheck(PTY_AtomicBuffer);
          }
          // init Wasm Finish notify
          else if (d.cmd === "initWasmDone") {
            console.log(`workerId ${d.workerId} is ready.`);
            if (!initProcessInitialized) {
              initWasmDoneNum++;
              if (initWasmDoneNum === userBinList.length * this.dupWorkerNum) {
                // start init process after all initial workers created.
                newProcess(initProcessJsPath, false);
                initProcessInitialized = true;
              }
            }
          }
          // exit handling
          else if (d.cmd === "exitSuccess") {
            exitHandling(d.workerId);
            this.rebootWorker(d.workerId);
          }
          // unknown cmd.
          else {
            throw e;
          }

          tEcvPid = -1;
        };
      },
      async createWasmModules(binList) {
        for (let ELF_Bin of binList) {
          try {
            let wasmPath = ELF_Bin + ".wasm";
            const url = new URL(wasmPath, import.meta.url).href;
            const resp = await fetch(url, { credentials: "same-origin" });
            const wasmBytes = await resp.arrayBuffer();
            const wasmModule = await WebAssembly.compile(wasmBytes);

            this.wasmModules.set(wasmPath, wasmModule);

          } catch (reason) {
            err(`wasm streaming compile failed: ${reason}`);
            err("falling back to ArrayBuffer instantiation");
          }
        }
      },
    };

    function newSession(pid) {
      return {
        sessionId: pid,
        controllingTTY: TTY.ttys[FS.makedev(5, 0)], // /dev/tty
      };
    }

    // system call handling.
    function runSyscall(d) {
      gWasmMemory = processes.get(d.ecvPid).wasmMemory;
      updateMemoryViews(gWasmMemory);

      let m32View = new Int32Array(gWasmMemory.buffer);

      let headPtr32 = d.spHead32;
      let sysNum = m32View[headPtr32];
      let argsNum = m32View[headPtr32 + 1];

      let sysRvalPtr = headPtr32 + 2 + argsNum;
      let waitPtr = sysRvalPtr + 1;

      let sysArgs = new Int32Array(argsNum);

      for (var i = 0; i < argsNum; i++) {
        sysArgs[i] = m32View[headPtr32 + 2 + i];
      }

      let tgtKernelFunction = SysFuncMap.get(sysNum);
      if (!tgtKernelFunction) {
        throw new Error(`unknown syscall: ${sysNum}`);
      }
      if (tgtKernelFunction.length != argsNum) {
        throw new Error(`argsNum (${argsNum}) must be equal to the args number (length: ${tgtKernelFunction.length}) of the syscall (sysNum: ${sysNum}).`);
      }

      // call the target kernel function.
      let sysRval = tgtKernelFunction(...sysArgs);

      // support async syscall handlers (e.g. poll with timeout)
      if (sysRval instanceof Promise) {
        sysRval.then(val => {
          m32View[sysRvalPtr] = val;
          Atomics.store(m32View, waitPtr, 1);
          Atomics.notify(m32View, waitPtr, 1);
        });
      } else {
        // store the return value of syscall function executing.
        m32View[sysRvalPtr] = sysRval;

        // notify to process worker
        Atomics.store(m32View, waitPtr, 1);
        Atomics.notify(m32View, waitPtr, 1);
      }
    }

    function exitHandling(workerId) {
      let tWorkerInfo = WORKER_MGR.workerInfoPool[workerId];
      tWorkerInfo.memory = WORKER_MGR.newProcessMemory(INITIAL_MEMORY_SIZE);
      // set the worker status `S_STOP`
      tWorkerInfo.status = WORKER_MGR.S_STOP;
    }

    function randInt(min, max) {
      return Math.floor(Math.random() * (max - min + 1)) + min;
    }

    function randU32() {
      return Math.floor(Math.random() * 0x100000000);
    }

    function createTaskStruct(pid, comm, state, ppid, pgrp, session, starttime, pwd) {
      return {
          /* pid */ pid: pid,
          /* comm */ comm: comm,
          /* state */ state: state,
          /* ppid */ ppid: ppid,
          /* pgrp */ pgrp: pgrp,
          /* session */ session: session,

        tty_nr: 0,
        tpgid: -1,
        flags: randU32(),

        minflt: randInt(0, 200000),
        cminflt: 0,
        majflt: randInt(0, 5000),
        cmajflt: 0,

        utime: randInt(0, 1000),
        stime: randInt(0, 1000),
        cutime: 0,
        cstime: 0,

        priority: randInt(-20, 19),
        nice: randInt(-20, 19),

        num_threads: randInt(1, 64),
        itrealvalue: 0,

          /* starttime */ starttime: starttime,

        vsize: randInt(1 << 20, 4 << 30),
        rss: randInt(0, 200000),
        rsslim: "18446744073709551615",

        startcode: 0,
        endcode: 0,
        startstack: 0,

        kstkesp: 0,
        kstkeip: 0,

        signal: 0,
        blocked: 0,
        sigignore: 0,
        sigcatch: 0,

        wchan: 0,
        nswap: 0,
        cnswap: 0,

        exit_signal: 17,
        processor: randInt(0, 7),

        rt_priority: 0,
        policy: 0,

        delayacct_blkio_ticks: 0,
        guest_time: 0,
        cguest_time: 0,

        start_data: 0,
        end_data: 0,
        start_brk: 0,

        arg_start: 0,
        arg_end: 0,
        env_start: 0,
        env_end: 0,

        exit_code: 0,
        fs_struct: {
          root: `/`,
          pwd: pwd,
        },
      };
    }

    // create new process
    // We assumes that init Wasm process (!isForked) already has `session` and `controlling terminal`
    // and the assumption is likely acceptable for many Linux processes.
    function newProcess(jsPath, isForked, parEcvPid, sDataSrcP, sDataLen, mBytesSrcP, mBytesLen) {

      // various ids.
      let ecvPid = getNewEcvPid();
      let ecvParPid = isForked ? parEcvPid : 0;
      let ecvPgid = isForked ? processes.get(parEcvPid).ecvPgid : ecvPid;
      // assumes that session has been set, so init Wasm call `newSession` instead of `undefined`.
      let session = isForked ? processes.get(parEcvPid).session : newSession(ecvPid);

      tEcvPid = ecvPid;

      // init FD table.
      FS.initFDTable(ecvPid, ecvParPid);
      // create taskStruct.
      let cmdline = isForked ? processes.get(ecvParPid).task.comm : Module["initProgram"].slice(0, -5);
      let pwd = isForked ? processes.get(ecvParPid).task.fs_struct.pwd : `/`;
      let taskStruct = createTaskStruct(ecvPid, cmdline, 'R', ecvParPid, ecvPgid, session.pid, Math.floor((Date.now() - jsKernelBootMs) * CLK_TCK / 1000), pwd);

      // procfs settings
      if (isForked) {
        PROCFS.createMyProc(ecvPid);
      } else {
        PROCFS.init(ecvPid);
      }

      if (!isForked) {
        // init standard stream.
        FS.initStandardStream();
        // register foreground process group for controlling terminal.
        session.controllingTTY.fgPgid = ecvPgid;
      }

      // shared array buffer for synchronous process between js-kernel and process-worker.
      let copyFinBell = new SharedArrayBuffer(4);
      // [0]. 0: initial, 1: execve success, 2: fail, 3: copy success 
      // [1]: used for returning `argc` to the new execved process worker.
      let execveBuf = new SharedArrayBuffer(8);
      // child monitoring ring buffer.
      // [RingBufferLock (4 byte); Empty (4 byte); head (4 byte); tail (4 byte); [ecvPid list] (4 * (childProcessMax + 1)) byte)]  // child processes is 20 at maximum
      // RingBufferLock. 0: Free, 1: Lock
      let childMonitor = (() => { let childMonitor = new SharedArrayBuffer(4 * 4 + 4 * (childProcessMax + 1)); let view = new Int32Array(childMonitor); view.set([0, 1, 0, 0], 0); return childMonitor })();
      let parMonitor = isForked ? processes.get(parEcvPid).childMonitor : undefined;

      let wasmProgram = isForked ? processes.get(parEcvPid).wasmProgram : Module["initProgram"];

      // get or init Worker (Wasm module initialization should start at this point)
      let workerInfo = WORKER_MGR.getAvailableWorkerInfo(jsPath);
      let processWorker = workerInfo.worker;
      let newWMemory = workerInfo.memory;

      // add fork state copy handling to the message handling.
      if (isForked) {
        let initialMsgHandling = processWorker.onmessage;
        processWorker.onmessage = e => {
          let d = e["data"];

          tEcvPid = d.ecvPid;

          if (d.cmd === "forkMemoryCopy") {
            let parWMemory = processes.get(parEcvPid).wasmMemory;
            // copy `memory_arena_bytes`
            let parWMemory8_1 = new Uint8Array(parWMemory.buffer);
            (growMemViews(newWMemory), HEAPU8).set(parWMemory8_1.subarray(mBytesSrcP, mBytesSrcP + mBytesLen), d.mBytesDstP);
            // write `child_pid` and `parent_pid` to the shared data buffer before copy.
            let parWMemory32 = new Uint32Array(parWMemory.buffer);
            parWMemory32[sDataSrcP + (sDataLen - 12) >> 2] = ecvPid;
            parWMemory32[sDataSrcP + (sDataLen - 8) >> 2] = parEcvPid;
            parWMemory32[sDataSrcP + (sDataLen - 4) >> 2] = ecvPgid;
            // copy `shared_data`
            let parWMemory8_2 = new Uint8Array(parWMemory.buffer);
            (growMemViews(newWMemory), HEAPU8).set(parWMemory8_2.subarray(sDataSrcP, sDataSrcP + sDataLen), d.sDataDstP);

            // update processes relatioinship.
            processes.get(parEcvPid).childs.add(tEcvPid);

            // notify to parent process worker.
            let parBellView = new Int32Array(processes.get(parEcvPid).copyFinBell);
            Atomics.store(parBellView, 0, 1);
            Atomics.notify(parBellView, 0, 1);

            // notify to this process worker.
            let chBellView = new Int32Array(copyFinBell);
            Atomics.store(chBellView, 0, 1);
            Atomics.notify(chBellView, 0, 1);
          } else {
            initialMsgHandling(e);
          }

          tEcvPid = -1;
        }
      }

      processes.set(ecvPid, {
        ecvPid: ecvPid,
        ecvParPid: ecvParPid,
        ecvPgid: ecvPgid,
        session: session,
        task: taskStruct,
        wasmProgram: wasmProgram,
        worker: processWorker,
        wasmMemory: newWMemory,
        copyFinBell: copyFinBell,
        execveBuf: execveBuf,
        parent: isForked ? parEcvPid : undefined,
        childs: new Set(),
        childMonitor: childMonitor,
        parMonitor: parMonitor,
      });

      // start this process.
      processWorker.postMessage({
        cmd: "startProcess",
        processType: isForked ? "forked" : "init",
        ecvPid: ecvPid,
        wasmMemory: newWMemory,
        copyFinBell: copyFinBell,
        childMonitor: childMonitor,
        parMonitor: parMonitor,
        execveBuf: execveBuf,
        PTY_AtomicBuffer: PTY_AtomicBuffer,
        FIFO_AtomicBuf: FIFO_AtomicBuf,
      });

      return ecvPid;
    }

    function preRun() {
      if (Module["preRun"]) {
        if (typeof Module["preRun"] == "function") Module["preRun"] = [Module["preRun"]];
        while (Module["preRun"].length) {
          addOnPreRun(Module["preRun"].shift())
        }
      }
      callRuntimeCallbacks(onPreRuns)
    }

    async function initRuntime() {
      TTY.init(); // actually, this do nothing.
      FS.ignorePermissions = false
      await WORKER_MGR.createWasmModules(userBinList);
      WORKER_MGR.init(userBinList);
      jsKernelBootMs = Date.now();
    }

    function preMain() { }

    function postRun() {
      if (Module["postRun"]) {
        if (typeof Module["postRun"] == "function") Module["postRun"] = [Module["postRun"]];
        while (Module["postRun"].length) {
          addOnPostRun(Module["postRun"].shift())
        }
      }
      callRuntimeCallbacks(onPostRuns)
    }
    var runDependencies = 0;
    var dependenciesFulfilled = null;

    function getUniqueRunDependency(id) {
      return id
    }

    function addRunDependency(id) {
      runDependencies++;
      Module["monitorRunDependencies"]?.(runDependencies)
    }

    function removeRunDependency(id) {
      runDependencies--;
      Module["monitorRunDependencies"]?.(runDependencies);
      if (runDependencies == 0) {
        if (dependenciesFulfilled) {
          var callback = dependenciesFulfilled;
          dependenciesFulfilled = null;
          callback()
        }
      }
    }

    function abort(what) {
      Module["onAbort"]?.(what);
      what = "Aborted(" + what + ")";
      err(what);
      ABORT = true;
      what += ". Build with -sASSERTIONS for more info.";
      var e = new WebAssembly.RuntimeError(what);
      readyPromiseReject(e);
      throw e
    }

    const ECV_IO_SETUP = 0;
    const ECV_IO_DESTROY = 1;
    const ECV_IO_SUBMIT = 2;
    const ECV_IO_CANCEL = 3;
    const ECV_IO_GETEVENTS = 4;
    const ECV_SETXATTR = 5;
    const ECV_LSETXATTR = 6;
    const ECV_FSETXATTR = 7;
    const ECV_GETXATTR = 8;
    const ECV_LGETXATTR = 9;
    const ECV_FGETXATTR = 10;
    const ECV_LISTXATTR = 11;
    const ECV_LLISTXATTR = 12;
    const ECV_FLISTXATTR = 13;
    const ECV_REMOVEXATTR = 14;
    const ECV_LREMOVEXATTR = 15;
    const ECV_FREMOVEXATTR = 16;
    const ECV_GETCWD = 17;
    const ECV_LOOKUP_DCOOKIE = 18;
    const ECV_EVENTFD2 = 19;
    const ECV_EPOLL_CREATE1 = 20;
    const ECV_EPOLL_CTL = 21;
    const ECV_EPOLL_PWAIT = 22;
    const ECV_DUP = 23;
    const ECV_DUP3 = 24;
    const ECV_FCNTL = 25;
    const ECV_INOTIFY_INIT1 = 26;
    const ECV_INOTIFY_ADD_WATCH = 27;
    const ECV_INOTIFY_RM_WATCH = 28;
    const ECV_IOCTL = 29;
    const ECV_IOPRIO_SET = 30;
    const ECV_IOPRIO_GET = 31;
    const ECV_FLOCK = 32;
    const ECV_MKNODAT = 33;
    const ECV_MKDIRAT = 34;
    const ECV_UNLINKAT = 35;
    const ECV_SYMLINKAT = 36;
    const ECV_LINKAT = 37;
    const ECV_RENAMEAT = 38;
    const ECV_UMOUNT2 = 39;
    const ECV_MOUNT = 40;
    const ECV_PIVOT_ROOT = 41;
    const ECV_NFSSERVCTL = 42;
    const ECV_STATFS = 43;
    const ECV_FSTATFS = 44;
    const ECV_TRUNCATE = 45;
    const ECV_FTRUNCATE = 46;
    const ECV_FALLOCATE = 47;
    const ECV_FACCESSAT = 48;
    const ECV_CHDIR = 49;
    const ECV_FCHDIR = 50;
    const ECV_CHROOT = 51;
    const ECV_FCHMOD = 52;
    const ECV_FCHMODAT = 53;
    const ECV_FCHOWNAT = 54;
    const ECV_FCHOWN = 55;
    const ECV_OPENAT = 56;
    const ECV_CLOSE = 57;
    const ECV_VHANGUP = 58;
    const ECV_PIPE2 = 59;
    const ECV_QUOTACTL = 60;
    const ECV_GETDENTS = 61;
    const ECV_LSEEK = 62;
    const ECV_READ = 63;
    const ECV_WRITE = 64;
    const ECV_READV = 65;
    const ECV_WRITEV = 66;
    const ECV_PREAD = 67;
    const ECV_PWRITE = 68;
    const ECV_PREADV = 69;
    const ECV_PWRITEV = 70;
    const ECV_SENDFILE = 71;
    // const ECV_PSELECT6 = 72; // no need
    // const ECV_PPOLL = 73; // no need
    const ECV_SIGNALFD4 = 74;
    const ECV_VMSPLICE = 75;
    const ECV_SPLICE = 76;
    const ECV_TEE = 77;
    const ECV_READLINKAT = 78;
    const ECV_NEWFSTATAT = 79;
    const ECV_NEWFSTAT = 80;
    const ECV_SYNC = 81;
    const ECV_FSYNC = 82;
    const ECV_FDATASYNC = 83;
    const ECV_SYNC_FILE_RANGE = 84;
    const ECV_TIMERFD_CREATE = 85;
    const ECV_TIMERFD_SETTIME = 86;
    const ECV_TIMERFD_GETTIME = 87;
    const ECV_UTIMENSAT = 88;
    const ECV_ACCT = 89;
    const ECV_CAPGET = 90;
    const ECV_CAPSET = 91;
    const ECV_PERSONALITY = 92;
    const ECV_EXIT = 93;
    const ECV_EXIT_GROUP = 94;
    const ECV_WAITID = 95;
    const ECV_SET_TID_ADDRESS = 96;
    const ECV_UNSHARE = 97;
    const ECV_FUTEX = 98;
    const ECV_SET_ROBUST_LIST = 99;
    const ECV_GET_ROBUST_LIST = 100;
    const ECV_NANOSLEEP = 101;
    const ECV_GETITIMER = 102;
    const ECV_SETITIMER = 103;
    const ECV_KEXEC_LOAD = 104;
    const ECV_INIT_MODULE = 105;
    const ECV_DELETE_MODULE = 106;
    const ECV_TIMER_CREATE = 107;
    const ECV_TIMER_GETTIME = 108;
    const ECV_TIMER_GETOVERRUN = 109;
    const ECV_TIMER_SETTIME = 110;
    const ECV_TIMER_DELETE = 111;
    const ECV_CLOCK_SETTIME = 112;
    const ECV_CLOCK_GETTIME = 113;
    const ECV_CLOCK_GETRES = 114;
    const ECV_CLOCK_NANOSLEEP = 115;
    const ECV_SYSLOG = 116;
    const ECV_PTRACE = 117;
    const ECV_SCHED_SETPARAM = 118;
    const ECV_SCHED_SETSCHEDULER = 119;
    const ECV_SCHED_GETSCHEDULER = 120;
    const ECV_SCHED_GETPARAM = 121;
    const ECV_SCHED_SETAFFINITY = 122;
    const ECV_SCHED_GETAFFINITY = 123;
    const ECV_SCHED_YIELD = 124;
    const ECV_SCHED_GET_PRIORITY_MAX = 125;
    const ECV_SCHED_GET_PRIORITY_MIN = 126;
    const ECV_SCHED_RR_GET_INTERVAL = 127;
    const ECV_RESTART_SYSCALL = 128;
    const ECV_KILL = 129;
    const ECV_TKILL = 130;
    const ECV_TGKILL = 131;
    const ECV_SIGALTSTACK = 132;
    const ECV_RT_SIGSUSPEND = 133;
    const ECV_RT_SIGACTION = 134;
    const ECV_RT_SIGPROCMASK = 135;
    const ECV_RT_SIGPENDING = 136;
    const ECV_RT_SIGTIMEDWAIT = 137;
    const ECV_RT_SIGQUEUEINFO = 138;
    const ECV_RT_SIGRETURN = 139;
    const ECV_SETPRIORITY = 140;
    const ECV_GETPRIORITY = 141;
    const ECV_REBOOT = 142;
    const ECV_SETREGID = 143;
    const ECV_SETGID = 144;
    const ECV_SETREUID = 145;
    const ECV_SETUID = 146;
    const ECV_SETRESUID = 147;
    const ECV_GETRESUID = 148;
    const ECV_SETRESGID = 149;
    const ECV_GETRESGID = 150;
    const ECV_SETFSUID = 151;
    const ECV_SETFSGID = 152;
    const ECV_TIMES = 153;
    const ECV_SETPGID = 154;
    const ECV_GETPGID = 155;
    const ECV_GETSID = 156;
    const ECV_SETSID = 157;
    const ECV_GETGROUPS = 158;
    const ECV_SETGROUPS = 159;
    const ECV_UNAME = 160;
    const ECV_SETHOSTNAME = 161;
    const ECV_SETDOMAINNAME = 162;
    const ECV_GETRLIMIT = 163;
    const ECV_SETRLIMIT = 164;
    const ECV_GETRUSAGE = 165;
    const ECV_UMASK = 166;
    const ECV_PRCTL = 167;
    const ECV_GETCPU = 168;
    const ECV_GETTIMEOFDAY = 169;
    const ECV_SETTIMEOFDAY = 170;
    const ECV_ADJTIMEX = 171;
    const ECV_GETPID = 172;
    const ECV_GETPPID = 173;
    const ECV_GETUID = 174;
    const ECV_GETEUID = 175;
    const ECV_GETGID = 176;
    const ECV_GETEGID = 177;
    const ECV_GETTID = 178;
    const ECV_SYSINFO = 179;
    const ECV_MQ_OPEN = 180;
    const ECV_MQ_UNLINK = 181;
    const ECV_MQ_TIMEDSEND = 182;
    const ECV_MQ_TIMEDRECEIVE = 183;
    const ECV_MQ_NOTIFY = 184;
    const ECV_MQ_GETSETATTR = 185;
    const ECV_MSGGET = 186;
    const ECV_MSGCTL = 187;
    const ECV_MSGRCV = 188;
    const ECV_MSGSND = 189;
    const ECV_SEMGET = 190;
    const ECV_SEMCTL = 191;
    const ECV_SEMTIMEDOP = 192;
    const ECV_SEMOP = 193;
    const ECV_SHMGET = 194;
    const ECV_SHMCTL = 195;
    const ECV_SHMAT = 196;
    const ECV_SHMDT = 197;
    const ECV_SOCKET = 198;
    const ECV_SOCKETPAIR = 199;
    const ECV_BIND = 200;
    const ECV_LISTEN = 201;
    const ECV_ACCEPT = 202;
    const ECV_CONNECT = 203;
    const ECV_GETSOCKNAME = 204;
    const ECV_GETPEERNAME = 205;
    const ECV_SENDTO = 206;
    const ECV_RECVFROM = 207;
    const ECV_SETSOCKOPT = 208;
    const ECV_GETSOCKOPT = 209;
    const ECV_SHUTDOWN = 210;
    const ECV_SENDMSG = 211;
    const ECV_RECVMSG = 212;
    const ECV_READAHEAD = 213;
    const ECV_BRK = 214;
    const ECV_MUNMAP = 215;
    const ECV_MREMAP = 216;
    const ECV_ADD_KEY = 217;
    const ECV_REQUEST_KEY = 218;
    const ECV_KEYCTL = 219;
    const ECV_CLONE = 220;
    const ECV_EXECVE = 221;
    const ECV_MMAP = 222;
    const ECV_FADVISE64 = 223;
    const ECV_SWAPON = 224;
    const ECV_SWAPOFF = 225;
    const ECV_MPROTECT = 226;
    const ECV_MSYNC = 227;
    const ECV_MLOCK = 228;
    const ECV_MUNLOCK = 229;
    const ECV_MLOCKALL = 230;
    const ECV_MUNLOCKALL = 231;
    const ECV_MINCORE = 232;
    const ECV_MADVISE = 233;
    const ECV_REMAP_FILE_PAGES = 234;
    const ECV_MBIND = 235;
    const ECV_GET_MEMPOLICY = 236;
    const ECV_SET_MEMPOLICY = 237;
    const ECV_MIGRATE_PAGES = 238;
    const ECV_MOVE_PAGES = 239;
    const ECV_RT_TGSIGQUEUEINFO = 240;
    const ECV_PERF_EVENT_OPEN = 241;
    const ECV_ACCEPT4 = 242;
    const ECV_RECVMMSG = 243;
    const ECV_WAIT4 = 260;
    const ECV_PRLIMIT64 = 261;
    const ECV_FANOTIFY_INIT = 262;
    const ECV_FANOTIFY_MARK = 263;
    const ECV_NAME_TO_HANDLE_AT = 264;
    const ECV_OPEN_BY_HANDLE_AT = 265;
    const ECV_CLOCK_ADJTIME = 266;
    const ECV_SYNCFS = 267;
    const ECV_SETNS = 268;
    const ECV_SENDMMSG = 269;
    const ECV_PROCESS_VM_READV = 270;
    const ECV_PROCESS_VM_WRITEV = 271;
    const ECV_KCMP = 272;
    const ECV_FINIT_MODULE = 273;
    const ECV_SCHED_SETATTR = 274;
    const ECV_SCHED_GETATTR = 275;
    const ECV_RENAMEAT2 = 276;
    const ECV_SECCOMP = 277;
    const ECV_GETRANDOM = 278;
    const ECV_MEMFD_CREATE = 279;
    const ECV_BPF = 280;
    const ECV_EXECVEAT = 281;
    const ECV_USERFAULTFD = 282;
    const ECV_MEMBARRIER = 283;
    const ECV_MLOCK2 = 284;
    const ECV_COPY_FILE_RANGE = 285;
    const ECV_PREADV2 = 286;
    const ECV_PWRITEV2 = 287;
    const ECV_PKEY_MPROTECT = 288;
    const ECV_PKEY_ALLOC = 289;
    const ECV_PKEY_FREE = 290;
    const ECV_STATX = 291;
    const ECV_IO_PGETEVENTS = 292;
    const ECV_RSEQ = 293;
    const ECV_KEXEC_FILE_LOAD = 294;
    const ECV_PIDFD_SEND_SIGNAL = 424;
    const ECV_IO_URING_SETUP = 425;
    const ECV_IO_URING_ENTER = 426;
    const ECV_IO_URING_REGISTER = 427;
    const ECV_OPEN_TREE = 428;
    const ECV_MOVE_MOUNT = 429;
    const ECV_FSOPEN = 430;
    const ECV_FSCONFIG = 431;
    const ECV_FSMOUNT = 432;
    const ECV_FSPICK = 433;
    const ECV_PIDFD_OPEN = 434;
    const ECV_CLONE3 = 435;
    const ECV_CLOSE_RANGE = 436;
    const ECV_OPENAT2 = 437;
    const ECV_PIDFD_GETFD = 438;
    const ECV_FACCESSAT2 = 439;
    const ECV_PROCESS_MADVISE = 440;
    const ECV_EPOLL_PWAIT2 = 441;
    const ECV_MOUNT_SETATTR = 442;
    const ECV_QUOTACTL_FD = 443;
    const ECV_LANDLOCK_CREATE_RULESET = 444;
    const ECV_LANDLOCK_ADD_RULE = 445;
    const ECV_LANDLOCK_RESTRICT_SELF = 446;
    const ECV_MEMFD_SECRET = 447;
    const ECV_PROCESS_MRELEASE = 448;
    const ECV_FUTEX_WAITV = 449;

    // macro specified to the emscripten runtime
    const ECV_LSTAT64 = 10000;
    // const ECV_ENVIRON_GET = 10001;
    // const ECV_ENVIRON_SIZES_GET = 10002;

    // select/poll
    const ECV_POLL_SCAN = 10003;
    const ECV_PSELECT6_SCAN = 10004;

    // pipe2
    const ECV_GET_DEV_TYPE = 10005;
    const ECV_FIFO_READ = 10006;
    const ECV_FIFO_WRITE = 10007;

    // emscripten-specific syscalls (not in Linux AArch64 table)
    const ECV_CHMOD = 10008;
    const ECV_FD_FDSTAT_GET = 10009;

    SysFuncMap.set(ECV_CLONE, ___syscall_clone);
    SysFuncMap.set(ECV_WAIT4, ___syscall_wait4);
    SysFuncMap.set(ECV_EXECVE, ___syscall_execve);
    SysFuncMap.set(ECV_CHDIR, ___syscall_chdir);
    SysFuncMap.set(ECV_DUP, ___syscall_dup);
    SysFuncMap.set(ECV_DUP3, ___syscall_dup3);
    SysFuncMap.set(ECV_FACCESSAT, ___syscall_faccessat);
    SysFuncMap.set(ECV_FCNTL, ___syscall_fcntl64);
    SysFuncMap.set(ECV_NEWFSTAT, ___syscall_fstat64);
    SysFuncMap.set(ECV_FTRUNCATE, ___syscall_ftruncate64);
    SysFuncMap.set(ECV_GETCWD, ___syscall_getcwd);
    SysFuncMap.set(ECV_GETDENTS, ___syscall_getdents64);
    SysFuncMap.set(ECV_IOCTL, ___syscall_ioctl);
    SysFuncMap.set(ECV_MKDIRAT, ___syscall_mkdirat);
    SysFuncMap.set(ECV_NEWFSTATAT, ___syscall_newfstatat);
    SysFuncMap.set(ECV_OPENAT, ___syscall_openat);
    SysFuncMap.set(ECV_SENDFILE, ___syscall_sendfile);
    // unused.
    // SysFuncMap.set(ECV_PPOLL, ___syscall_poll);
    SysFuncMap.set(ECV_READLINKAT, ___syscall_readlinkat);
    SysFuncMap.set(ECV_STATX, ___syscall_stat64);
    SysFuncMap.set(ECV_STATFS, ___syscall_statfs64);
    SysFuncMap.set(ECV_TRUNCATE, ___syscall_truncate64);
    SysFuncMap.set(ECV_UNLINKAT, ___syscall_unlinkat);
    SysFuncMap.set(ECV_UTIMENSAT, ___syscall_utimensat);
    SysFuncMap.set(ECV_CLOSE, _fd_close);
    SysFuncMap.set(ECV_PIPE2, ___syscall_pipe2);
    SysFuncMap.set(ECV_READ, _fd_read);
    SysFuncMap.set(ECV_PREAD, _fd_pread);
    SysFuncMap.set(ECV_LSEEK, _fd_seek);
    SysFuncMap.set(ECV_WRITE, _fd_write);
    SysFuncMap.set(ECV_PWRITE, _fd_pwrite);
    SysFuncMap.set(ECV_EXIT, ___syscall_exit);
    SysFuncMap.set(ECV_GETRANDOM, _random_get);
    SysFuncMap.set(ECV_SETPGID, ___syscall_setpgid);
    SysFuncMap.set(ECV_GETPGID, ___syscall_getpgid);

    // emscripten runtimes
    SysFuncMap.set(ECV_LSTAT64, ___syscall_lstat64);
    // SysFuncMap.set(ECV_ENVIRON_GET, 1001);
    // SysFuncMap.set(ECV_ENVIRON_SIZES_GET, 1002);

    // select/poll
    SysFuncMap.set(ECV_POLL_SCAN, ___syscall_poll_scan);
    SysFuncMap.set(ECV_PSELECT6_SCAN, ___syscall_pselect6_scan);

    // read/write for pipe2
    SysFuncMap.set(ECV_GET_DEV_TYPE, ___ecv_get_dev_type);
    SysFuncMap.set(ECV_FIFO_READ, _fd_fifo_read);
    SysFuncMap.set(ECV_FIFO_WRITE, _fd_fifo_write);

    // new filesystem syscalls
    SysFuncMap.set(ECV_CHMOD, ___syscall_chmod);
    SysFuncMap.set(ECV_FCHMOD, ___syscall_fchmod);
    SysFuncMap.set(ECV_FCHMODAT, ___syscall_fchmodat);
    SysFuncMap.set(ECV_FCHOWNAT, ___syscall_fchownat);
    SysFuncMap.set(ECV_FDATASYNC, ___syscall_fdatasync);
    SysFuncMap.set(ECV_RENAMEAT, ___syscall_renameat);
    SysFuncMap.set(ECV_SYMLINKAT, ___syscall_symlinkat);
    SysFuncMap.set(ECV_FD_FDSTAT_GET, _fd_fdstat_get);


    class ExitStatus {
      name = "ExitStatus";
      constructor(status) {
        this.message = `Program terminated with exit(${status})`;
        this.status = status
      }
    }
    var callRuntimeCallbacks = callbacks => {
      while (callbacks.length > 0) {
        callbacks.shift()(Module)
      }
    };
    var onPostRuns = [];
    var addOnPostRun = cb => onPostRuns.push(cb);
    var onPreRuns = [];
    var addOnPreRun = cb => onPreRuns.push(cb);
    var noExitRuntime = true;

    class ExceptionInfo {
      constructor(excPtr) {
        this.excPtr = excPtr;
        this.ptr = excPtr - 24
      }
      set_type(type) {
        (growMemViews(gWasmMemory), HEAPU32)[this.ptr + 4 >> 2] = type
      }
      get_type() {
        return (growMemViews(gWasmMemory), HEAPU32)[this.ptr + 4 >> 2]
      }
      set_destructor(destructor) {
        (growMemViews(gWasmMemory), HEAPU32)[this.ptr + 8 >> 2] = destructor
      }
      get_destructor() {
        return (growMemViews(gWasmMemory), HEAPU32)[this.ptr + 8 >> 2]
      }
      set_caught(caught) {
        caught = caught ? 1 : 0;
        (growMemViews(gWasmMemory), HEAP8)[this.ptr + 12] = caught
      }
      get_caught() {
        return (growMemViews(gWasmMemory), HEAP8)[this.ptr + 12] != 0
      }
      set_rethrown(rethrown) {
        rethrown = rethrown ? 1 : 0;
        (growMemViews(gWasmMemory), HEAP8)[this.ptr + 13] = rethrown
      }
      get_rethrown() {
        return (growMemViews(gWasmMemory), HEAP8)[this.ptr + 13] != 0
      }
      init(type, destructor) {
        this.set_adjusted_ptr(0);
        this.set_type(type);
        this.set_destructor(destructor)
      }
      set_adjusted_ptr(adjustedPtr) {
        (growMemViews(gWasmMemory), HEAPU32)[this.ptr + 16 >> 2] = adjustedPtr
      }
      get_adjusted_ptr() {
        return (growMemViews(gWasmMemory), HEAPU32)[this.ptr + 16 >> 2]
      }
    }
    var exceptionLast = 0;
    var uncaughtExceptionCount = 0;
    var ___cxa_throw = (ptr, type, destructor) => {
      var info = new ExceptionInfo(ptr);
      info.init(type, destructor);
      exceptionLast = ptr;
      uncaughtExceptionCount++;
      throw exceptionLast
    };
    var PATH = {
      isAbs: path => path.charAt(0) === "/",
      splitPath: filename => {
        var splitPathRe = /^(\/?|)([\s\S]*?)((?:\.{1,2}|[^\/]+?|)(\.[^.\/]*|))(?:[\/]*)$/;
        return splitPathRe.exec(filename).slice(1)
      },
      normalizeArray: (parts, allowAboveRoot) => {
        var up = 0;
        for (var i = parts.length - 1; i >= 0; i--) {
          var last = parts[i];
          if (last === ".") {
            parts.splice(i, 1)
          } else if (last === "..") {
            parts.splice(i, 1);
            up++
          } else if (up) {
            parts.splice(i, 1);
            up--
          }
        }
        if (allowAboveRoot) {
          for (; up; up--) {
            parts.unshift("..")
          }
        }
        return parts
      },
      normalize: path => {
        var isAbsolute = PATH.isAbs(path),
          trailingSlash = path.slice(-1) === "/";
        path = PATH.normalizeArray(path.split("/").filter(p => !!p), !isAbsolute).join("/");
        if (!path && !isAbsolute) {
          path = "."
        }
        if (path && trailingSlash) {
          path += "/"
        }
        return (isAbsolute ? "/" : "") + path
      },
      dirname: path => {
        var result = PATH.splitPath(path),
          root = result[0],
          dir = result[1];
        if (!root && !dir) {
          return "."
        }
        if (dir) {
          dir = dir.slice(0, -1)
        }
        return root + dir
      },
      basename: path => path && path.match(/([^\/]+|\/)\/*$/)[1],
      join: (...paths) => PATH.normalize(paths.join("/")),
      join2: (l, r) => PATH.normalize(l + "/" + r)
    };
    var initRandomFill = () => view => crypto.getRandomValues(view);
    var randomFill = view => {
      (randomFill = initRandomFill())(view)
    };
    var PATH_FS = {
      resolve: (...args) => {
        var resolvedPath = "",
          resolvedAbsolute = false;
        for (var i = args.length - 1; i >= -1 && !resolvedAbsolute; i--) {
          var path = i >= 0 ? args[i] : FS.cwd();
          if (typeof path != "string") {
            throw new TypeError("Arguments to path.resolve must be strings")
          } else if (!path) {
            return ""
          }
          resolvedPath = path + "/" + resolvedPath;
          resolvedAbsolute = PATH.isAbs(path)
        }
        resolvedPath = PATH.normalizeArray(resolvedPath.split("/").filter(p => !!p), !resolvedAbsolute).join("/");
        return (resolvedAbsolute ? "/" : "") + resolvedPath || "."
      },
      relative: (from, to) => {
        from = PATH_FS.resolve(from).slice(1);
        to = PATH_FS.resolve(to).slice(1);

        function trim(arr) {
          var start = 0;
          for (; start < arr.length; start++) {
            if (arr[start] !== "") break
          }
          var end = arr.length - 1;
          for (; end >= 0; end--) {
            if (arr[end] !== "") break
          }
          if (start > end) return [];
          return arr.slice(start, end - start + 1)
        }
        var fromParts = trim(from.split("/"));
        var toParts = trim(to.split("/"));
        var length = Math.min(fromParts.length, toParts.length);
        var samePartsLength = length;
        for (var i = 0; i < length; i++) {
          if (fromParts[i] !== toParts[i]) {
            samePartsLength = i;
            break
          }
        }
        var outputParts = [];
        for (var i = samePartsLength; i < fromParts.length; i++) {
          outputParts.push("..")
        }
        outputParts = outputParts.concat(toParts.slice(samePartsLength));
        return outputParts.join("/")
      }
    };
    var UTF8Decoder = typeof TextDecoder != "undefined" ? new TextDecoder : undefined;
    var UTF8ArrayToString = (heapOrArray, idx = 0, maxBytesToRead = NaN) => {
      var endIdx = idx + maxBytesToRead;
      var endPtr = idx;
      while (heapOrArray[endPtr] && !(endPtr >= endIdx)) ++endPtr;
      if (endPtr - idx > 16 && heapOrArray.buffer && UTF8Decoder) {
        return UTF8Decoder.decode(heapOrArray.buffer instanceof ArrayBuffer ? heapOrArray.subarray(idx, endPtr) : heapOrArray.slice(idx, endPtr))
      }
      var str = "";
      while (idx < endPtr) {
        var u0 = heapOrArray[idx++];
        if (!(u0 & 128)) {
          str += String.fromCharCode(u0);
          continue
        }
        var u1 = heapOrArray[idx++] & 63;
        if ((u0 & 224) == 192) {
          str += String.fromCharCode((u0 & 31) << 6 | u1);
          continue
        }
        var u2 = heapOrArray[idx++] & 63;
        if ((u0 & 240) == 224) {
          u0 = (u0 & 15) << 12 | u1 << 6 | u2
        } else {
          u0 = (u0 & 7) << 18 | u1 << 12 | u2 << 6 | heapOrArray[idx++] & 63
        }
        if (u0 < 65536) {
          str += String.fromCharCode(u0)
        } else {
          var ch = u0 - 65536;
          str += String.fromCharCode(55296 | ch >> 10, 56320 | ch & 1023)
        }
      }
      return str
    };
    var PTY_signalNameToCode = {
      SIGINT: 2,
      SIGQUIT: 3,
      SIGTSTP: 20,
      SIGWINCH: 28
    };
    var PTY = Module["pty"];
    var PTY_AtomicBuffer = new SharedArrayBuffer(4);
    var PTY_pollTimeout = 0;
    var PTY_askToWaitAgain = timeout => {
      PTY_pollTimeout = timeout;
      throw new FS.ErrnoError(1006)
    };
    var lengthBytesUTF8 = str => {
      var len = 0;
      for (var i = 0; i < str.length; ++i) {
        var c = str.charCodeAt(i);
        if (c <= 127) {
          len++
        } else if (c <= 2047) {
          len += 2
        } else if (c >= 55296 && c <= 57343) {
          len += 4;
          ++i
        } else {
          len += 3
        }
      }
      return len
    };
    var stringToUTF8Array = (str, heap, outIdx, maxBytesToWrite) => {
      if (!(maxBytesToWrite > 0)) return 0;
      var startIdx = outIdx;
      var endIdx = outIdx + maxBytesToWrite - 1;
      for (var i = 0; i < str.length; ++i) {
        var u = str.charCodeAt(i);
        if (u >= 55296 && u <= 57343) {
          var u1 = str.charCodeAt(++i);
          u = 65536 + ((u & 1023) << 10) | u1 & 1023
        }
        if (u <= 127) {
          if (outIdx >= endIdx) break;
          heap[outIdx++] = u
        } else if (u <= 2047) {
          if (outIdx + 1 >= endIdx) break;
          heap[outIdx++] = 192 | u >> 6;
          heap[outIdx++] = 128 | u & 63
        } else if (u <= 65535) {
          if (outIdx + 2 >= endIdx) break;
          heap[outIdx++] = 224 | u >> 12;
          heap[outIdx++] = 128 | u >> 6 & 63;
          heap[outIdx++] = 128 | u & 63
        } else {
          if (outIdx + 3 >= endIdx) break;
          heap[outIdx++] = 240 | u >> 18;
          heap[outIdx++] = 128 | u >> 12 & 63;
          heap[outIdx++] = 128 | u >> 6 & 63;
          heap[outIdx++] = 128 | u & 63
        }
      }
      heap[outIdx] = 0;
      return outIdx - startIdx
    };
    var intArrayFromString = (stringy, dontAddNull, length) => {
      var len = length > 0 ? length : lengthBytesUTF8(stringy) + 1;
      var u8array = new Array(len);
      var numBytesWritten = stringToUTF8Array(stringy, u8array, 0, u8array.length);
      if (dontAddNull) u8array.length = numBytesWritten;
      return u8array
    };
    var TTY = {
      ttys: [],
      init() { },
      shutdown() { },
      register(dev, ops) {
        TTY.ttys[dev] = {
          input: [],
          output: [],
          fgPgid: null,
          ops
        };
        FS.registerDevice(dev, TTY.stream_ops)
      },
      stream_ops: {
        open(stream) {
          var tty = TTY.ttys[stream.node.rdev];
          if (!tty) {
            throw new FS.ErrnoError(43)
          }
          stream.tty = tty;
          stream.seekable = false
        },
        close(stream) {
          stream.tty.ops.fsync(stream.tty)
        },
        fsync(stream) {
          stream.tty.ops.fsync(stream.tty)
        },
        read: (stream, buffer, offset, length) => {
          let readBytes = PTY.read(length);
          if (length && !readBytes.length) {
            PTY_askToWaitAgain(-1)
          }
          buffer.set(readBytes, offset);
          return readBytes.length
        },
        write: (stream, buffer, offset, length) => {
          if (buffer === (growMemViews(gWasmMemory), HEAP8)) {
            buffer = (growMemViews(gWasmMemory), HEAPU8);
          } else if (!(buffer instanceof Uint8Array)) {
            throw new Error(`Unexpected buffer type: ${buffer.constructor.name}`)
          }
          let arr = Array.from(buffer.subarray(offset, offset + length));
          PTY.write(arr);
          return length
        },
        poll: (stream, events, timeout) => {
          let readyEvents = () => ((events & POLLIN) && PTY.readable) || ((events & POLLOUT) && PTY.writable);
          if (!readyEvents() && timeout) {
            PTY_askToWaitAgain(timeout);
          }
          return (((events & POLLIN) && PTY.readable) ? POLLIN : 0) | (((events & POLLOUT) && PTY.writable) ? POLLOUT : 0);
        }
      },
      default_tty_ops: {
        get_char() { },
        put_char() { },
        fsync() { },
        ioctl_tcgets: () => {
          const termios = PTY.ioctl("TCGETS");
          const data = {
            c_iflag: termios.iflag,
            c_oflag: termios.oflag,
            c_cflag: termios.cflag,
            c_lflag: termios.lflag,
            c_cc: termios.cc
          };
          return data
        },
        ioctl_tcsets: (_tty, _optional_actions, data) => {
          PTY.ioctl("TCSETS", {
            iflag: data.c_iflag,
            oflag: data.c_oflag,
            cflag: data.c_cflag,
            lflag: data.c_lflag,
            cc: data.c_cc
          });
          return 0
        },
        ioctl_tiocgwinsz: () => PTY.ioctl("TIOCGWINSZ").reverse()
      },
      default_tty1_ops: {
        put_char(tty, val) {
          if (val === null || val === 10) {
            err(UTF8ArrayToString(tty.output));
            tty.output = []
          } else {
            if (val != 0) tty.output.push(val)
          }
        },
        fsync(tty) {
          if (tty.output?.length > 0) {
            err(UTF8ArrayToString(tty.output));
            tty.output = []
          }
        }
      }
    };
    var mmapAlloc = size => {
      abort()
    };
    var MEMFS = {
      ops_table: null,
      mount(mount) {
        return MEMFS.createNode(null, "/", 16895, 0)
      },
      createNode(parent, name, mode, dev) {
        if (FS.isBlkdev(mode) || FS.isFIFO(mode)) {
          throw new FS.ErrnoError(63)
        }
        MEMFS.ops_table ||= {
          dir: {
            node: {
              getattr: MEMFS.node_ops.getattr,
              setattr: MEMFS.node_ops.setattr,
              lookup: MEMFS.node_ops.lookup,
              mknod: MEMFS.node_ops.mknod,
              rename: MEMFS.node_ops.rename,
              unlink: MEMFS.node_ops.unlink,
              rmdir: MEMFS.node_ops.rmdir,
              readdir: MEMFS.node_ops.readdir,
              symlink: MEMFS.node_ops.symlink
            },
            stream: {
              llseek: MEMFS.stream_ops.llseek
            }
          },
          file: {
            node: {
              getattr: MEMFS.node_ops.getattr,
              setattr: MEMFS.node_ops.setattr
            },
            stream: {
              llseek: MEMFS.stream_ops.llseek,
              read: MEMFS.stream_ops.read,
              write: MEMFS.stream_ops.write,
              mmap: MEMFS.stream_ops.mmap,
              msync: MEMFS.stream_ops.msync
            }
          },
          link: {
            node: {
              getattr: MEMFS.node_ops.getattr,
              setattr: MEMFS.node_ops.setattr,
              readlink: MEMFS.node_ops.readlink
            },
            stream: {}
          },
          chrdev: {
            node: {
              getattr: MEMFS.node_ops.getattr,
              setattr: MEMFS.node_ops.setattr
            },
            stream: FS.chrdev_stream_ops
          },
          fifo: {
            node: {
              getattr: MEMFS.node_ops.getattr,
              setattr: MEMFS.node_ops.setattr
            },
            stream: {
              read: MEMFS.stream_ops.read,
              write: MEMFS.stream_ops.write
            }
          }
        };
        var node = FS.createNode(parent, name, mode, dev);
        if (FS.isDir(node.mode)) {
          node.node_ops = MEMFS.ops_table.dir.node;
          node.stream_ops = MEMFS.ops_table.dir.stream;
          node.contents = {}
        } else if (FS.isFile(node.mode)) {
          node.node_ops = MEMFS.ops_table.file.node;
          node.stream_ops = MEMFS.ops_table.file.stream;
          node.usedBytes = 0;
          node.contents = null
        } else if (FS.isLink(node.mode)) {
          node.node_ops = MEMFS.ops_table.link.node;
          node.stream_ops = MEMFS.ops_table.link.stream
        } else if (FS.isChrdev(node.mode)) {
          node.node_ops = MEMFS.ops_table.chrdev.node;
          node.stream_ops = MEMFS.ops_table.chrdev.stream
        } else if (FS.isFIFO(node.mode)) {
          node.node_ops = MEMFS.ops_table.fifo.node;
          node.stream_ops = MEMFS.ops_table.fifo.stream;
        }
        node.atime = node.mtime = node.ctime = Date.now();
        if (parent) {
          parent.contents[name] = node;
          parent.atime = parent.mtime = parent.ctime = node.atime
        }
        return node
      },
      getFileDataAsTypedArray(node) {
        if (!node.contents) return new Uint8Array(0);
        if (node.contents.subarray) return node.contents.subarray(0, node.usedBytes);
        return new Uint8Array(node.contents)
      },
      expandFileStorage(node, newCapacity) {
        var prevCapacity = node.contents ? node.contents.length : 0;
        if (prevCapacity >= newCapacity) return;
        var CAPACITY_DOUBLING_MAX = 1024 * 1024;
        newCapacity = Math.max(newCapacity, prevCapacity * (prevCapacity < CAPACITY_DOUBLING_MAX ? 2 : 1.125) >>> 0);
        if (prevCapacity != 0) newCapacity = Math.max(newCapacity, 256);
        var oldContents = node.contents;
        node.contents = new Uint8Array(newCapacity);
        if (node.usedBytes > 0) node.contents.set(oldContents.subarray(0, node.usedBytes), 0)
      },
      resizeFileStorage(node, newSize) {
        if (node.usedBytes == newSize) return;
        if (newSize == 0) {
          node.contents = null;
          node.usedBytes = 0
        } else {
          var oldContents = node.contents;
          node.contents = new Uint8Array(newSize);
          if (oldContents) {
            node.contents.set(oldContents.subarray(0, Math.min(newSize, node.usedBytes)))
          }
          node.usedBytes = newSize
        }
      },
      node_ops: {
        getattr(node) {
          var attr = {};
          attr.dev = FS.isChrdev(node.mode) ? node.id : 1;
          attr.ino = node.id;
          attr.mode = node.mode;
          attr.nlink = 1;
          attr.uid = 0;
          attr.gid = 0;
          attr.rdev = node.rdev;
          if (FS.isDir(node.mode)) {
            attr.size = 4096
          } else if (FS.isFile(node.mode)) {
            attr.size = node.usedBytes
          } else if (FS.isLink(node.mode)) {
            attr.size = node.link.length
          } else {
            attr.size = 0
          }
          attr.atime = new Date(node.atime);
          attr.mtime = new Date(node.mtime);
          attr.ctime = new Date(node.ctime);
          attr.blksize = 4096;
          attr.blocks = Math.ceil(attr.size / attr.blksize);
          return attr
        },
        setattr(node, attr) {
          for (const key of ["mode", "atime", "mtime", "ctime"]) {
            if (attr[key] != null) {
              node[key] = attr[key]
            }
          }
          if (attr.size !== undefined) {
            MEMFS.resizeFileStorage(node, attr.size)
          }
        },
        lookup(parent, name) {
          throw MEMFS.doesNotExistError
        },
        mknod(parent, name, mode, dev) {
          return MEMFS.createNode(parent, name, mode, dev)
        },
        rename(old_node, new_dir, new_name) {
          var new_node;
          try {
            new_node = FS.lookupNode(new_dir, new_name)
          } catch (e) { }
          if (new_node) {
            if (FS.isDir(old_node.mode)) {
              for (var i in new_node.contents) {
                throw new FS.ErrnoError(55)
              }
            }
            FS.hashRemoveNode(new_node)
          }
          delete old_node.parent.contents[old_node.name];
          new_dir.contents[new_name] = old_node;
          old_node.name = new_name;
          new_dir.ctime = new_dir.mtime = old_node.parent.ctime = old_node.parent.mtime = Date.now()
        },
        unlink(parent, name) {
          delete parent.contents[name];
          parent.ctime = parent.mtime = Date.now()
        },
        rmdir(parent, name) {
          var node = FS.lookupNode(parent, name);
          for (var i in node.contents) {
            throw new FS.ErrnoError(55)
          }
          delete parent.contents[name];
          parent.ctime = parent.mtime = Date.now()
        },
        readdir(node) {
          return [".", "..", ...Object.keys(node.contents)]
        },
        symlink(parent, newname, oldpath) {
          var node = MEMFS.createNode(parent, newname, 511 | 40960, 0);
          node.link = oldpath;
          return node
        },
        readlink(node) {
          if (!FS.isLink(node.mode)) {
            throw new FS.ErrnoError(28)
          }
          return node.link
        }
      },
      stream_ops: {
        read(stream, buffer, offset, length, position) {
          var contents = stream.node.contents;
          if (position >= stream.node.usedBytes) return 0;
          var size = Math.min(stream.node.usedBytes - position, length);
          if (size > 8 && contents.subarray) {
            buffer.set(contents.subarray(position, position + size), offset)
          } else {
            for (var i = 0; i < size; i++) buffer[offset + i] = contents[position + i]
          }
          return size
        },
        write(stream, buffer, offset, length, position, canOwn) {
          if (buffer.buffer === (growMemViews(gWasmMemory), HEAP8).buffer) {
            canOwn = false
          }
          if (!length) return 0;
          var node = stream.node;
          node.mtime = node.ctime = Date.now();
          if (buffer.subarray && (!node.contents || node.contents.subarray)) {
            if (canOwn) {
              node.contents = buffer.subarray(offset, offset + length);
              node.usedBytes = length;
              return length
            } else if (node.usedBytes === 0 && position === 0) {
              node.contents = buffer.slice(offset, offset + length);
              node.usedBytes = length;
              return length
            } else if (position + length <= node.usedBytes) {
              node.contents.set(buffer.subarray(offset, offset + length), position);
              return length
            }
          }
          MEMFS.expandFileStorage(node, position + length);
          if (node.contents.subarray && buffer.subarray) {
            node.contents.set(buffer.subarray(offset, offset + length), position)
          } else {
            for (var i = 0; i < length; i++) {
              node.contents[position + i] = buffer[offset + i]
            }
          }
          node.usedBytes = Math.max(node.usedBytes, position + length);
          return length
        },
        llseek(stream, offset, whence) {
          var position = offset;
          if (whence === 1) {
            position += stream.position
          } else if (whence === 2) {
            if (FS.isFile(stream.node.mode)) {
              position += stream.node.usedBytes
            }
          }
          if (position < 0) {
            throw new FS.ErrnoError(28)
          }
          return position
        },
        mmap(stream, length, position, prot, flags) {
          if (!FS.isFile(stream.node.mode)) {
            throw new FS.ErrnoError(43)
          }
          var ptr;
          var allocated;
          var contents = stream.node.contents;
          if (!(flags & 2) && contents && contents.buffer === (growMemViews(gWasmMemory), HEAP8).buffer) {
            allocated = false;
            ptr = contents.byteOffset
          } else {
            allocated = true;
            ptr = mmapAlloc(length);
            if (!ptr) {
              throw new FS.ErrnoError(48)
            }
            if (contents) {
              if (position > 0 || position + length < contents.length) {
                if (contents.subarray) {
                  contents = contents.subarray(position, position + length)
                } else {
                  contents = Array.prototype.slice.call(contents, position, position + length)
                }
              }
              (growMemViews(gWasmMemory), HEAP8).set(contents, ptr)
            }
          }
          return {
            ptr,
            allocated
          }
        },
        msync(stream, buffer, offset, length, mmapFlags) {
          MEMFS.stream_ops.write(stream, buffer, 0, length, offset, false);
          return 0
        }
      }
    };
    var asyncLoad = async url => {
      var arrayBuffer = await readAsync(url);
      return new Uint8Array(arrayBuffer)
    };
    var FS_createDataFile = (...args) => FS.createDataFile(...args);
    var preloadPlugins = [];
    var FS_handledByPreloadPlugin = (byteArray, fullname, finish, onerror) => {
      if (typeof Browser != "undefined") Browser.init();
      var handled = false;
      preloadPlugins.forEach(plugin => {
        if (handled) return;
        if (plugin["canHandle"](fullname)) {
          plugin["handle"](byteArray, fullname, finish, onerror);
          handled = true
        }
      });
      return handled
    };
    var FS_createPreloadedFile = (parent, name, url, canRead, canWrite, onload, onerror, dontCreateFile, canOwn, preFinish) => {
      var fullname = name ? PATH_FS.resolve(PATH.join2(parent, name)) : parent;
      var dep = getUniqueRunDependency(`cp ${fullname}`);

      function processData(byteArray) {
        function finish(byteArray) {
          preFinish?.();
          if (!dontCreateFile) {
            FS_createDataFile(parent, name, byteArray, canRead, canWrite, canOwn)
          }
          onload?.();
          removeRunDependency(dep)
        }
        if (FS_handledByPreloadPlugin(byteArray, fullname, finish, () => {
          onerror?.();
          removeRunDependency(dep)
        })) {
          return
        }
        finish(byteArray)
      }
      addRunDependency(dep);
      if (typeof url == "string") {
        asyncLoad(url).then(processData, onerror)
      } else {
        processData(url)
      }
    };

    // Add FS.createPath function for loadPackage compatibility
    var FS_createPath = (parent, path, canRead, canWrite) => {
      var fullPath = parent === "/" ? "/" + path : parent + "/" + path;
      var parts = fullPath.split("/").filter(p => p);
      var currentPath = "";
      for (var i = 0; i < parts.length; i++) {
        currentPath += "/" + parts[i];
        try {
          FS.mkdir(currentPath);
        } catch (e) {
          // Ignore error if directory already exists
          if (e.errno !== 20) throw e;
        }
      }
    };

    // Expose addRunDependency and removeRunDependency for loadPackage
    Module["addRunDependency"] = addRunDependency;
    Module["removeRunDependency"] = removeRunDependency;
    Module["FS_createPath"] = FS_createPath;

    // Create a special version of FS_createDataFile that doesn't require FD table
    // This is needed for loadPackage which runs before process initialization
    Module["FS_createDataFile"] = (parent, name, data, canRead, canWrite, canOwn) => {
      var path = name;
      if (parent) {
        parent = typeof parent == "string" ? parent : FS.getPath(parent);
        path = name ? PATH.join2(parent, name) : parent
      }
      var mode = FS_getMode(canRead, canWrite);
      var node = FS.create(path, mode);
      if (data) {
        if (typeof data == "string") {
          var arr = new Array(data.length);
          for (var i = 0, len = data.length; i < len; ++i) arr[i] = data.charCodeAt(i);
          data = arr
        }
        // For MEMFS, directly set the contents without opening a stream
        if (node.node_ops && node.node_ops.setattr) {
          // Set contents directly on MEMFS node
          node.contents = new Uint8Array(data);
          node.usedBytes = data.length;
          node.timestamp = Date.now();
        } else {
          // Fallback: use the standard method (may fail if FD table not initialized)
          FS.chmod(node, mode | 146);
          var stream = FS.open(node, 577);
          FS.write(stream, data, 0, data.length, 0, canOwn);
          FS.close(stream.fd);
          FS.chmod(node, mode);
        }
      }
    };

    // Define loadPackage function (will be called from run())
    Module["expectedDataFileDownloads"] ??= 0;
    Module["loadPackage"] = function (metadata) {
      console.log("loadPackage called, Module.FS_createDataFile exists:", typeof Module["FS_createDataFile"]);
      console.log("FS exists:", typeof FS, "FS.createDataFile exists:", typeof FS?.createDataFile);
      var PACKAGE_PATH = "";
      if (typeof window === "object") {
        PACKAGE_PATH = window["encodeURIComponent"](window.location.pathname.substring(0, window.location.pathname.lastIndexOf("/")) + "/")
      } else if (typeof process === "undefined" && typeof location !== "undefined") {
        PACKAGE_PATH = encodeURIComponent(location.pathname.substring(0, location.pathname.lastIndexOf("/")) + "/")
      }
      var PACKAGE_NAME = "python.data";
      var REMOTE_PACKAGE_BASE = "python.data";
      var REMOTE_PACKAGE_NAME = Module["locateFile"] ? Module["locateFile"](REMOTE_PACKAGE_BASE, "") : REMOTE_PACKAGE_BASE;
      var REMOTE_PACKAGE_SIZE = metadata["remote_package_size"];

      function fetchRemotePackage(packageName, packageSize, callback, errback) {
        Module["dataFileDownloads"] ??= {};
        fetch(packageName).then(response => {
          if (!response.ok) {
            errback?.(new Error(`${response.status}: ${response.url}`));
            return;
          }
          if (!response.body && response.arrayBuffer) {
            return response.arrayBuffer().then(callback, errback)
          }
          const reader = response.body.getReader();
          const chunks = [];
          const headers = response.headers;
          const total = Number(headers.get("Content-Length") ?? packageSize);
          let loaded = 0;

          const handleChunk = ({ done, value }) => {
            if (!done) {
              chunks.push(value);
              loaded += value.length;
              Module["dataFileDownloads"][packageName] = {
                loaded,
                total
              };
              let totalLoaded = 0;
              let totalSize = 0;
              for (const download of Object.values(Module["dataFileDownloads"])) {
                totalLoaded += download.loaded;
                totalSize += download.total
              }
              Module["setStatus"]?.(`Downloading data... (${totalLoaded}/${totalSize})`);
              return reader.read().then(handleChunk, errback);
            } else {
              const packageData = new Uint8Array(chunks.map(c => c.length).reduce((a, b) => a + b, 0));
              let offset = 0;
              for (const chunk of chunks) {
                packageData.set(chunk, offset);
                offset += chunk.length
              }
              callback(packageData.buffer);
            }
          };

          Module["setStatus"]?.("Downloading data...");
          reader.read().then(handleChunk, errback);
        }).catch(cause => {
          errback?.(new Error(`Network Error: ${packageName}`, { cause }));
        })
      }

      function handleError(error) {
        console.error("package error:", error)
      }
      var fetchedCallback = null;
      var fetched = Module["getPreloadedPackage"] ? Module["getPreloadedPackage"](REMOTE_PACKAGE_NAME, REMOTE_PACKAGE_SIZE) : null;
      if (!fetched) fetchRemotePackage(REMOTE_PACKAGE_NAME, REMOTE_PACKAGE_SIZE, data => {
        if (fetchedCallback) {
          fetchedCallback(data);
          fetchedCallback = null
        } else {
          fetched = data
        }
      }, handleError);

      var runWithFSExecuted = false;
      function runWithFS(Module) {
        // Ensure runWithFS is executed only once
        if (runWithFSExecuted) {
          return;
        }
        runWithFSExecuted = true;

        function assert(check, msg) {
          if (!check) throw msg + (new Error).stack
        }
        Module["FS_createPath"]("/lib", "python3.15", true, true);
        Module["FS_createPath"]("/lib/python3.15", "lib-dynload", true, true);
        Module["FS_createPath"]("/lib/python3.15", "__phello__", true, true);
        Module["FS_createPath"]("/lib/python3.15/__phello__", "ham", true, true);
        Module["FS_createPath"]("/lib/python3.15", "__pycache__", true, true);
        Module["FS_createPath"]("/lib/python3.15", "_pyrepl", true, true);
        Module["FS_createPath"]("/lib/python3.15/_pyrepl", "__pycache__", true, true);
        Module["FS_createPath"]("/lib/python3.15", "asyncio", true, true);
        Module["FS_createPath"]("/lib/python3.15/asyncio", "__pycache__", true, true);
        Module["FS_createPath"]("/lib/python3.15", "collections", true, true);
        Module["FS_createPath"]("/lib/python3.15/collections", "__pycache__", true, true);
        Module["FS_createPath"]("/lib/python3.15", "compression", true, true);
        Module["FS_createPath"]("/lib/python3.15/compression", "__pycache__", true, true);
        Module["FS_createPath"]("/lib/python3.15/compression", "_common", true, true);
        Module["FS_createPath"]("/lib/python3.15/compression/_common", "__pycache__", true, true);
        Module["FS_createPath"]("/lib/python3.15/compression", "zstd", true, true);
        Module["FS_createPath"]("/lib/python3.15/compression/zstd", "__pycache__", true, true);
        Module["FS_createPath"]("/lib/python3.15", "concurrent", true, true);
        Module["FS_createPath"]("/lib/python3.15/concurrent", "__pycache__", true, true);
        Module["FS_createPath"]("/lib/python3.15/concurrent", "futures", true, true);
        Module["FS_createPath"]("/lib/python3.15/concurrent/futures", "__pycache__", true, true);
        Module["FS_createPath"]("/lib/python3.15/concurrent", "interpreters", true, true);
        Module["FS_createPath"]("/lib/python3.15", "ctypes", true, true);
        Module["FS_createPath"]("/lib/python3.15/ctypes", "macholib", true, true);
        Module["FS_createPath"]("/lib/python3.15", "curses", true, true);
        Module["FS_createPath"]("/lib/python3.15", "dbm", true, true);
        Module["FS_createPath"]("/lib/python3.15", "email", true, true);
        Module["FS_createPath"]("/lib/python3.15/email", "mime", true, true);
        Module["FS_createPath"]("/lib/python3.15", "encodings", true, true);
        Module["FS_createPath"]("/lib/python3.15/encodings", "__pycache__", true, true);
        Module["FS_createPath"]("/lib/python3.15", "ensurepip", true, true);
        Module["FS_createPath"]("/lib/python3.15/ensurepip", "_bundled", true, true);
        Module["FS_createPath"]("/lib/python3.15", "html", true, true);
        Module["FS_createPath"]("/lib/python3.15", "http", true, true);
        Module["FS_createPath"]("/lib/python3.15", "idlelib", true, true);
        Module["FS_createPath"]("/lib/python3.15/idlelib", "Icons", true, true);
        Module["FS_createPath"]("/lib/python3.15/idlelib", "idle_test", true, true);
        Module["FS_createPath"]("/lib/python3.15", "importlib", true, true);
        Module["FS_createPath"]("/lib/python3.15/importlib", "__pycache__", true, true);
        Module["FS_createPath"]("/lib/python3.15/importlib", "metadata", true, true);
        Module["FS_createPath"]("/lib/python3.15/importlib", "resources", true, true);
        Module["FS_createPath"]("/lib/python3.15", "json", true, true);
        Module["FS_createPath"]("/lib/python3.15/json", "__pycache__", true, true);
        Module["FS_createPath"]("/lib/python3.15", "logging", true, true);
        Module["FS_createPath"]("/lib/python3.15/logging", "__pycache__", true, true);
        Module["FS_createPath"]("/lib/python3.15", "multiprocessing", true, true);
        Module["FS_createPath"]("/lib/python3.15/multiprocessing", "dummy", true, true);
        Module["FS_createPath"]("/lib/python3.15", "pathlib", true, true);
        Module["FS_createPath"]("/lib/python3.15/pathlib", "__pycache__", true, true);
        Module["FS_createPath"]("/lib/python3.15", "profiling", true, true);
        Module["FS_createPath"]("/lib/python3.15/profiling", "sampling", true, true);
        Module["FS_createPath"]("/lib/python3.15/profiling/sampling", "_assets", true, true);
        Module["FS_createPath"]("/lib/python3.15/profiling/sampling", "_flamegraph_assets", true, true);
        Module["FS_createPath"]("/lib/python3.15/profiling/sampling", "_heatmap_assets", true, true);
        Module["FS_createPath"]("/lib/python3.15/profiling/sampling", "_shared_assets", true, true);
        Module["FS_createPath"]("/lib/python3.15/profiling/sampling", "_vendor", true, true);
        Module["FS_createPath"]("/lib/python3.15/profiling/sampling/_vendor", "d3-flame-graph", true, true);
        Module["FS_createPath"]("/lib/python3.15/profiling/sampling/_vendor/d3-flame-graph", "4.1.3", true, true);
        Module["FS_createPath"]("/lib/python3.15/profiling/sampling/_vendor", "d3", true, true);
        Module["FS_createPath"]("/lib/python3.15/profiling/sampling/_vendor/d3", "7.8.5", true, true);
        Module["FS_createPath"]("/lib/python3.15/profiling/sampling", "live_collector", true, true);
        Module["FS_createPath"]("/lib/python3.15/profiling", "tracing", true, true);
        Module["FS_createPath"]("/lib/python3.15", "pydoc_data", true, true);
        Module["FS_createPath"]("/lib/python3.15", "re", true, true);
        Module["FS_createPath"]("/lib/python3.15/re", "__pycache__", true, true);
        Module["FS_createPath"]("/lib/python3.15", "site-packages", true, true);
        Module["FS_createPath"]("/lib/python3.15", "sqlite3", true, true);
        Module["FS_createPath"]("/lib/python3.15", "string", true, true);
        Module["FS_createPath"]("/lib/python3.15/string", "__pycache__", true, true);
        Module["FS_createPath"]("/lib/python3.15", "sysconfig", true, true);
        Module["FS_createPath"]("/lib/python3.15/sysconfig", "__pycache__", true, true);
        Module["FS_createPath"]("/lib/python3.15", "test", true, true);
        Module["FS_createPath"]("/lib/python3.15/test", "archivetestdata", true, true);
        Module["FS_createPath"]("/lib/python3.15/test", "audiodata", true, true);
        Module["FS_createPath"]("/lib/python3.15/test", "audit_test_data", true, true);
        Module["FS_createPath"]("/lib/python3.15/test", "certdata", true, true);
        Module["FS_createPath"]("/lib/python3.15/test/certdata", "capath", true, true);
        Module["FS_createPath"]("/lib/python3.15/test", "cjkencodings", true, true);
        Module["FS_createPath"]("/lib/python3.15/test", "configdata", true, true);
        Module["FS_createPath"]("/lib/python3.15/test", "crashers", true, true);
        Module["FS_createPath"]("/lib/python3.15/test", "data", true, true);
        Module["FS_createPath"]("/lib/python3.15/test", "decimaltestdata", true, true);
        Module["FS_createPath"]("/lib/python3.15/test", "dtracedata", true, true);
        Module["FS_createPath"]("/lib/python3.15/test", "encoded_modules", true, true);
        Module["FS_createPath"]("/lib/python3.15/test", "leakers", true, true);
        Module["FS_createPath"]("/lib/python3.15/test", "libregrtest", true, true);
        Module["FS_createPath"]("/lib/python3.15/test", "mathdata", true, true);
        Module["FS_createPath"]("/lib/python3.15/test", "regrtestdata", true, true);
        Module["FS_createPath"]("/lib/python3.15/test/regrtestdata", "import_from_tests", true, true);
        Module["FS_createPath"]("/lib/python3.15/test/regrtestdata/import_from_tests", "test_regrtest_b", true, true);
        Module["FS_createPath"]("/lib/python3.15/test", "subprocessdata", true, true);
        Module["FS_createPath"]("/lib/python3.15/test", "support", true, true);
        Module["FS_createPath"]("/lib/python3.15/test/support", "_hypothesis_stubs", true, true);
        Module["FS_createPath"]("/lib/python3.15/test", "test_ast", true, true);
        Module["FS_createPath"]("/lib/python3.15/test/test_ast", "data", true, true);
        Module["FS_createPath"]("/lib/python3.15/test", "test_asyncio", true, true);
        Module["FS_createPath"]("/lib/python3.15/test", "test_capi", true, true);
        Module["FS_createPath"]("/lib/python3.15/test", "test_cext", true, true);
        Module["FS_createPath"]("/lib/python3.15/test", "test_concurrent_futures", true, true);
        Module["FS_createPath"]("/lib/python3.15/test", "test_cppext", true, true);
        Module["FS_createPath"]("/lib/python3.15/test", "test_ctypes", true, true);
        Module["FS_createPath"]("/lib/python3.15/test", "test_dataclasses", true, true);
        Module["FS_createPath"]("/lib/python3.15/test", "test_doctest", true, true);
        Module["FS_createPath"]("/lib/python3.15/test", "test_email", true, true);
        Module["FS_createPath"]("/lib/python3.15/test/test_email", "data", true, true);
        Module["FS_createPath"]("/lib/python3.15/test", "test_free_threading", true, true);
        Module["FS_createPath"]("/lib/python3.15/test", "test_future_stmt", true, true);
        Module["FS_createPath"]("/lib/python3.15/test", "test_gdb", true, true);
        Module["FS_createPath"]("/lib/python3.15/test", "test_import", true, true);
        Module["FS_createPath"]("/lib/python3.15/test/test_import", "data", true, true);
        Module["FS_createPath"]("/lib/python3.15/test/test_import/data", "circular_imports", true, true);
        Module["FS_createPath"]("/lib/python3.15/test/test_import/data/circular_imports", "subpkg", true, true);
        Module["FS_createPath"]("/lib/python3.15/test/test_import/data/circular_imports", "subpkg2", true, true);
        Module["FS_createPath"]("/lib/python3.15/test/test_import/data/circular_imports/subpkg2", "parent", true, true);
        Module["FS_createPath"]("/lib/python3.15/test/test_import/data", "package", true, true);
        Module["FS_createPath"]("/lib/python3.15/test/test_import/data", "package2", true, true);
        Module["FS_createPath"]("/lib/python3.15/test/test_import/data", "package3", true, true);
        Module["FS_createPath"]("/lib/python3.15/test/test_import/data", "package4", true, true);
        Module["FS_createPath"]("/lib/python3.15/test/test_import/data", "unwritable", true, true);
        Module["FS_createPath"]("/lib/python3.15/test", "test_importlib", true, true);
        Module["FS_createPath"]("/lib/python3.15/test/test_importlib", "builtin", true, true);
        Module["FS_createPath"]("/lib/python3.15/test/test_importlib", "extension", true, true);
        Module["FS_createPath"]("/lib/python3.15/test/test_importlib", "frozen", true, true);
        Module["FS_createPath"]("/lib/python3.15/test/test_importlib", "import_", true, true);
        Module["FS_createPath"]("/lib/python3.15/test/test_importlib", "metadata", true, true);
        Module["FS_createPath"]("/lib/python3.15/test/test_importlib/metadata", "data", true, true);
        Module["FS_createPath"]("/lib/python3.15/test/test_importlib/metadata/data", "sources", true, true);
        Module["FS_createPath"]("/lib/python3.15/test/test_importlib/metadata/data/sources", "example", true, true);
        Module["FS_createPath"]("/lib/python3.15/test/test_importlib/metadata/data/sources/example", "example", true, true);
        Module["FS_createPath"]("/lib/python3.15/test/test_importlib/metadata/data/sources", "example2", true, true);
        Module["FS_createPath"]("/lib/python3.15/test/test_importlib/metadata/data/sources/example2", "example2", true, true);
        Module["FS_createPath"]("/lib/python3.15/test/test_importlib", "namespace_pkgs", true, true);
        Module["FS_createPath"]("/lib/python3.15/test/test_importlib/namespace_pkgs", "both_portions", true, true);
        Module["FS_createPath"]("/lib/python3.15/test/test_importlib/namespace_pkgs/both_portions", "foo", true, true);
        Module["FS_createPath"]("/lib/python3.15/test/test_importlib/namespace_pkgs", "foo", true, true);
        Module["FS_createPath"]("/lib/python3.15/test/test_importlib/namespace_pkgs", "module_and_namespace_package", true, true);
        Module["FS_createPath"]("/lib/python3.15/test/test_importlib/namespace_pkgs/module_and_namespace_package", "a_test", true, true);
        Module["FS_createPath"]("/lib/python3.15/test/test_importlib/namespace_pkgs", "not_a_namespace_pkg", true, true);
        Module["FS_createPath"]("/lib/python3.15/test/test_importlib/namespace_pkgs/not_a_namespace_pkg", "foo", true, true);
        Module["FS_createPath"]("/lib/python3.15/test/test_importlib/namespace_pkgs", "portion1", true, true);
        Module["FS_createPath"]("/lib/python3.15/test/test_importlib/namespace_pkgs/portion1", "foo", true, true);
        Module["FS_createPath"]("/lib/python3.15/test/test_importlib/namespace_pkgs", "portion2", true, true);
        Module["FS_createPath"]("/lib/python3.15/test/test_importlib/namespace_pkgs/portion2", "foo", true, true);
        Module["FS_createPath"]("/lib/python3.15/test/test_importlib/namespace_pkgs", "project1", true, true);
        Module["FS_createPath"]("/lib/python3.15/test/test_importlib/namespace_pkgs/project1", "parent", true, true);
        Module["FS_createPath"]("/lib/python3.15/test/test_importlib/namespace_pkgs/project1/parent", "child", true, true);
        Module["FS_createPath"]("/lib/python3.15/test/test_importlib/namespace_pkgs", "project2", true, true);
        Module["FS_createPath"]("/lib/python3.15/test/test_importlib/namespace_pkgs/project2", "parent", true, true);
        Module["FS_createPath"]("/lib/python3.15/test/test_importlib/namespace_pkgs/project2/parent", "child", true, true);
        Module["FS_createPath"]("/lib/python3.15/test/test_importlib/namespace_pkgs", "project3", true, true);
        Module["FS_createPath"]("/lib/python3.15/test/test_importlib/namespace_pkgs/project3", "parent", true, true);
        Module["FS_createPath"]("/lib/python3.15/test/test_importlib/namespace_pkgs/project3/parent", "child", true, true);
        Module["FS_createPath"]("/lib/python3.15/test/test_importlib", "partial", true, true);
        Module["FS_createPath"]("/lib/python3.15/test/test_importlib", "resources", true, true);
        Module["FS_createPath"]("/lib/python3.15/test/test_importlib", "source", true, true);
        Module["FS_createPath"]("/lib/python3.15/test", "test_inspect", true, true);
        Module["FS_createPath"]("/lib/python3.15/test", "test_interpreters", true, true);
        Module["FS_createPath"]("/lib/python3.15/test", "test_io", true, true);
        Module["FS_createPath"]("/lib/python3.15/test", "test_json", true, true);
        Module["FS_createPath"]("/lib/python3.15/test", "test_module", true, true);
        Module["FS_createPath"]("/lib/python3.15/test", "test_multiprocessing_fork", true, true);
        Module["FS_createPath"]("/lib/python3.15/test", "test_multiprocessing_forkserver", true, true);
        Module["FS_createPath"]("/lib/python3.15/test", "test_multiprocessing_spawn", true, true);
        Module["FS_createPath"]("/lib/python3.15/test", "test_os", true, true);
        Module["FS_createPath"]("/lib/python3.15/test", "test_pathlib", true, true);
        Module["FS_createPath"]("/lib/python3.15/test/test_pathlib", "support", true, true);
        Module["FS_createPath"]("/lib/python3.15/test", "test_peg_generator", true, true);
        Module["FS_createPath"]("/lib/python3.15/test", "test_profiling", true, true);
        Module["FS_createPath"]("/lib/python3.15/test/test_profiling", "test_sampling_profiler", true, true);
        Module["FS_createPath"]("/lib/python3.15/test", "test_pydoc", true, true);
        Module["FS_createPath"]("/lib/python3.15/test", "test_pyrepl", true, true);
        Module["FS_createPath"]("/lib/python3.15/test", "test_sqlite3", true, true);
        Module["FS_createPath"]("/lib/python3.15/test", "test_string", true, true);
        Module["FS_createPath"]("/lib/python3.15/test", "test_tkinter", true, true);
        Module["FS_createPath"]("/lib/python3.15/test", "test_tomllib", true, true);
        Module["FS_createPath"]("/lib/python3.15/test/test_tomllib", "data", true, true);
        Module["FS_createPath"]("/lib/python3.15/test/test_tomllib/data", "invalid", true, true);
        Module["FS_createPath"]("/lib/python3.15/test/test_tomllib/data/invalid", "array-of-tables", true, true);
        Module["FS_createPath"]("/lib/python3.15/test/test_tomllib/data/invalid", "array", true, true);
        Module["FS_createPath"]("/lib/python3.15/test/test_tomllib/data/invalid", "boolean", true, true);
        Module["FS_createPath"]("/lib/python3.15/test/test_tomllib/data/invalid", "dates-and-times", true, true);
        Module["FS_createPath"]("/lib/python3.15/test/test_tomllib/data/invalid", "dotted-keys", true, true);
        Module["FS_createPath"]("/lib/python3.15/test/test_tomllib/data/invalid", "inline-table", true, true);
        Module["FS_createPath"]("/lib/python3.15/test/test_tomllib/data/invalid", "keys-and-vals", true, true);
        Module["FS_createPath"]("/lib/python3.15/test/test_tomllib/data/invalid", "literal-str", true, true);
        Module["FS_createPath"]("/lib/python3.15/test/test_tomllib/data/invalid", "multiline-basic-str", true, true);
        Module["FS_createPath"]("/lib/python3.15/test/test_tomllib/data/invalid", "multiline-literal-str", true, true);
        Module["FS_createPath"]("/lib/python3.15/test/test_tomllib/data/invalid", "table", true, true);
        Module["FS_createPath"]("/lib/python3.15/test/test_tomllib/data", "valid", true, true);
        Module["FS_createPath"]("/lib/python3.15/test/test_tomllib/data/valid", "array", true, true);
        Module["FS_createPath"]("/lib/python3.15/test/test_tomllib/data/valid", "dates-and-times", true, true);
        Module["FS_createPath"]("/lib/python3.15/test/test_tomllib/data/valid", "multiline-basic-str", true, true);
        Module["FS_createPath"]("/lib/python3.15/test", "test_tools", true, true);
        Module["FS_createPath"]("/lib/python3.15/test/test_tools", "i18n_data", true, true);
        Module["FS_createPath"]("/lib/python3.15/test/test_tools", "msgfmt_data", true, true);
        Module["FS_createPath"]("/lib/python3.15/test", "test_ttk", true, true);
        Module["FS_createPath"]("/lib/python3.15/test", "test_unittest", true, true);
        Module["FS_createPath"]("/lib/python3.15/test/test_unittest", "namespace_test_pkg", true, true);
        Module["FS_createPath"]("/lib/python3.15/test/test_unittest/namespace_test_pkg", "bar", true, true);
        Module["FS_createPath"]("/lib/python3.15/test/test_unittest/namespace_test_pkg", "noop", true, true);
        Module["FS_createPath"]("/lib/python3.15/test/test_unittest/namespace_test_pkg/noop", "no2", true, true);
        Module["FS_createPath"]("/lib/python3.15/test/test_unittest", "testmock", true, true);
        Module["FS_createPath"]("/lib/python3.15/test", "test_warnings", true, true);
        Module["FS_createPath"]("/lib/python3.15/test/test_warnings", "data", true, true);
        Module["FS_createPath"]("/lib/python3.15/test", "test_zipfile", true, true);
        Module["FS_createPath"]("/lib/python3.15/test/test_zipfile", "_path", true, true);
        Module["FS_createPath"]("/lib/python3.15/test", "test_zoneinfo", true, true);
        Module["FS_createPath"]("/lib/python3.15/test/test_zoneinfo", "data", true, true);
        Module["FS_createPath"]("/lib/python3.15/test", "tkinterdata", true, true);
        Module["FS_createPath"]("/lib/python3.15/test", "tokenizedata", true, true);
        Module["FS_createPath"]("/lib/python3.15/test", "tracedmodules", true, true);
        Module["FS_createPath"]("/lib/python3.15/test", "translationdata", true, true);
        Module["FS_createPath"]("/lib/python3.15/test/translationdata", "argparse", true, true);
        Module["FS_createPath"]("/lib/python3.15/test/translationdata", "getopt", true, true);
        Module["FS_createPath"]("/lib/python3.15/test/translationdata", "optparse", true, true);
        Module["FS_createPath"]("/lib/python3.15/test", "typinganndata", true, true);
        Module["FS_createPath"]("/lib/python3.15/test/typinganndata", "partialexecution", true, true);
        Module["FS_createPath"]("/lib/python3.15/test", "wheeldata", true, true);
        Module["FS_createPath"]("/lib/python3.15/test", "xmltestdata", true, true);
        Module["FS_createPath"]("/lib/python3.15/test/xmltestdata", "c14n-20", true, true);
        Module["FS_createPath"]("/lib/python3.15/test", "zipimport_data", true, true);
        Module["FS_createPath"]("/lib/python3.15", "tkinter", true, true);
        Module["FS_createPath"]("/lib/python3.15", "tomllib", true, true);
        Module["FS_createPath"]("/lib/python3.15", "turtledemo", true, true);
        Module["FS_createPath"]("/lib/python3.15", "unittest", true, true);
        Module["FS_createPath"]("/lib/python3.15", "urllib", true, true);
        Module["FS_createPath"]("/lib/python3.15", "venv", true, true);
        Module["FS_createPath"]("/lib/python3.15/venv", "scripts", true, true);
        Module["FS_createPath"]("/lib/python3.15/venv/scripts", "common", true, true);
        Module["FS_createPath"]("/lib/python3.15/venv/scripts", "nt", true, true);
        Module["FS_createPath"]("/lib/python3.15/venv/scripts", "posix", true, true);
        Module["FS_createPath"]("/lib/python3.15", "wsgiref", true, true);
        Module["FS_createPath"]("/lib/python3.15", "xml", true, true);
        Module["FS_createPath"]("/lib/python3.15/xml", "__pycache__", true, true);
        Module["FS_createPath"]("/lib/python3.15/xml", "dom", true, true);
        Module["FS_createPath"]("/lib/python3.15/xml", "etree", true, true);
        Module["FS_createPath"]("/lib/python3.15/xml/etree", "__pycache__", true, true);
        Module["FS_createPath"]("/lib/python3.15/xml", "parsers", true, true);
        Module["FS_createPath"]("/lib/python3.15/xml", "sax", true, true);
        Module["FS_createPath"]("/lib/python3.15", "xmlrpc", true, true);
        Module["FS_createPath"]("/lib/python3.15", "zipfile", true, true);
        Module["FS_createPath"]("/lib/python3.15/zipfile", "_path", true, true);
        Module["FS_createPath"]("/lib/python3.15", "zoneinfo", true, true);
        Module["FS_createPath"]("/lib/python3.15/zoneinfo", "__pycache__", true, true);

        function DataRequest(start, end, audio) {
          this.start = start;
          this.end = end;
          this.audio = audio
        }
        DataRequest.prototype = {
          requests: {},
          open: function (mode, name) {
            this.name = name;
            this.requests[name] = this;
            Module["addRunDependency"](`fp ${this.name}`)
          },
          send: function () { },
          onload: function () {
            var byteArray = this.byteArray.subarray(this.start, this.end);
            this.finish(byteArray)
          },
          finish: function (byteArray) {
            var that = this;
            Module["FS_createDataFile"](this.name, null, byteArray, true, true, true);
            Module["removeRunDependency"](`fp ${that.name}`);
            this.requests[this.name] = null
          }
        };
        var files = metadata["files"];
        for (var i = 0; i < files.length; ++i) {
          new DataRequest(files[i]["start"], files[i]["end"], files[i]["audio"] || 0).open("GET", files[i]["filename"])
        }

        function processPackageData(arrayBuffer) {
          assert(arrayBuffer, "Loading data file failed.");
          assert(arrayBuffer.constructor.name === ArrayBuffer.name, "bad input to processPackageData");
          var byteArray = new Uint8Array(arrayBuffer);
          DataRequest.prototype.byteArray = byteArray;
          var files = metadata["files"];
          for (var i = 0; i < files.length; ++i) {
            DataRequest.prototype.requests[files[i].filename].onload()
          }
          Module["FS_logStats"]?.();
          Module["removeRunDependency"]("datafile_/root/elfconv/build/bash-static.generated.data")
        }
        Module["addRunDependency"]("datafile_/root/elfconv/build/bash-static.generated.data");
        Module["preloadResults"] ??= {};
        Module["preloadResults"][PACKAGE_NAME] = {
          fromCache: false
        };
        if (fetched) {
          processPackageData(fetched);
          fetched = null
        } else {
          fetchedCallback = processPackageData
        }
      }
      // Call runWithFS immediately to set up file system structure and start loading
      runWithFS(Module);
    };

    // Store the Python library metadata
    Module["pythonLibraryMetadata"] = {
      files: [{
        filename: "/lib/python3.15/__future__.py",
        start: 0,
        end: 5218
      }, {
        filename: "/lib/python3.15/__hello__.py",
        start: 5218,
        end: 5445
      }, {
        filename: "/lib/python3.15/__phello__/__init__.py",
        start: 5445,
        end: 5542
      }, {
        filename: "/lib/python3.15/__phello__/ham/__init__.py",
        start: 5542,
        end: 5542
      }, {
        filename: "/lib/python3.15/__phello__/ham/eggs.py",
        start: 5542,
        end: 5542
      }, {
        filename: "/lib/python3.15/__phello__/spam.py",
        start: 5542,
        end: 5639
      }, {
        filename: "/lib/python3.15/__pycache__/__future__.cpython-315.pyc",
        start: 5639,
        end: 10415
      }, {
        filename: "/lib/python3.15/__pycache__/_collections_abc.cpython-315.pyc",
        start: 10415,
        end: 58924
      }, {
        filename: "/lib/python3.15/__pycache__/_colorize.cpython-315.pyc",
        start: 58924,
        end: 79036
      }, {
        filename: "/lib/python3.15/__pycache__/_compat_pickle.cpython-315.pyc",
        start: 79036,
        end: 86338
      }, {
        filename: "/lib/python3.15/__pycache__/_opcode_metadata.cpython-315.pyc",
        start: 86338,
        end: 96485
      }, {
        filename: "/lib/python3.15/__pycache__/_py_warnings.cpython-315.pyc",
        start: 96485,
        end: 136285
      }, {
        filename: "/lib/python3.15/__pycache__/_sitebuiltins.cpython-315.pyc",
        start: 136285,
        end: 141352
      }, {
        filename: "/lib/python3.15/__pycache__/_weakrefset.cpython-315.pyc",
        start: 141352,
        end: 150760
      }, {
        filename: "/lib/python3.15/__pycache__/abc.cpython-315.pyc",
        start: 150760,
        end: 158789
      }, {
        filename: "/lib/python3.15/__pycache__/annotationlib.cpython-315.pyc",
        start: 158789,
        end: 205556
      }, {
        filename: "/lib/python3.15/__pycache__/argparse.cpython-315.pyc",
        start: 205556,
        end: 323278
      }, {
        filename: "/lib/python3.15/__pycache__/ast.cpython-315.pyc",
        start: 323278,
        end: 354888
      }, {
        filename: "/lib/python3.15/__pycache__/bz2.cpython-315.pyc",
        start: 354888,
        end: 370195
      }, {
        filename: "/lib/python3.15/__pycache__/code.cpython-315.pyc",
        start: 370195,
        end: 386591
      }, {
        filename: "/lib/python3.15/__pycache__/codecs.cpython-315.pyc",
        start: 386591,
        end: 428489
      }, {
        filename: "/lib/python3.15/__pycache__/codeop.cpython-315.pyc",
        start: 428489,
        end: 435431
      }, {
        filename: "/lib/python3.15/__pycache__/contextlib.cpython-315.pyc",
        start: 435431,
        end: 466713
      }, {
        filename: "/lib/python3.15/__pycache__/contextvars.cpython-315.pyc",
        start: 466713,
        end: 467098
      }, {
        filename: "/lib/python3.15/__pycache__/copy.cpython-315.pyc",
        start: 467098,
        end: 477267
      }, {
        filename: "/lib/python3.15/__pycache__/copyreg.cpython-315.pyc",
        start: 477267,
        end: 485203
      }, {
        filename: "/lib/python3.15/__pycache__/dataclasses.cpython-315.pyc",
        start: 485203,
        end: 540090
      }, {
        filename: "/lib/python3.15/__pycache__/datetime.cpython-315.pyc",
        start: 540090,
        end: 540590
      }, {
        filename: "/lib/python3.15/__pycache__/difflib.cpython-315.pyc",
        start: 540590,
        end: 616345
      }, {
        filename: "/lib/python3.15/__pycache__/dis.cpython-315.pyc",
        start: 616345,
        end: 670630
      }, {
        filename: "/lib/python3.15/__pycache__/enum.cpython-315.pyc",
        start: 670630,
        end: 760810
      }, {
        filename: "/lib/python3.15/__pycache__/fnmatch.cpython-315.pyc",
        start: 760810,
        end: 768670
      }, {
        filename: "/lib/python3.15/__pycache__/functools.cpython-315.pyc",
        start: 768670,
        end: 816948
      }, {
        filename: "/lib/python3.15/__pycache__/genericpath.cpython-315.pyc",
        start: 816948,
        end: 825430
      }, {
        filename: "/lib/python3.15/__pycache__/gettext.cpython-315.pyc",
        start: 825430,
        end: 848687
      }, {
        filename: "/lib/python3.15/__pycache__/glob.cpython-315.pyc",
        start: 848687,
        end: 872538
      }, {
        filename: "/lib/python3.15/__pycache__/heapq.cpython-315.pyc",
        start: 872538,
        end: 891157
      }, {
        filename: "/lib/python3.15/__pycache__/inspect.cpython-315.pyc",
        start: 891157,
        end: 1031826
      }, {
        filename: "/lib/python3.15/__pycache__/keyword.cpython-315.pyc",
        start: 1031826,
        end: 1033355
      }, {
        filename: "/lib/python3.15/__pycache__/linecache.cpython-315.pyc",
        start: 1033355,
        end: 1043948
      }, {
        filename: "/lib/python3.15/__pycache__/locale.cpython-315.pyc",
        start: 1043948,
        end: 1104173
      }, {
        filename: "/lib/python3.15/__pycache__/lzma.cpython-315.pyc",
        start: 1104173,
        end: 1120660
      }, {
        filename: "/lib/python3.15/__pycache__/opcode.cpython-315.pyc",
        start: 1120660,
        end: 1125146
      }, {
        filename: "/lib/python3.15/__pycache__/operator.cpython-315.pyc",
        start: 1125146,
        end: 1144170
      }, {
        filename: "/lib/python3.15/__pycache__/os.cpython-315.pyc",
        start: 1144170,
        end: 1192499
      }, {
        filename: "/lib/python3.15/__pycache__/posixpath.cpython-315.pyc",
        start: 1192499,
        end: 1212559
      }, {
        filename: "/lib/python3.15/__pycache__/pprint.cpython-315.pyc",
        start: 1212559,
        end: 1246974
      }, {
        filename: "/lib/python3.15/__pycache__/reprlib.cpython-315.pyc",
        start: 1246974,
        end: 1258680
      }, {
        filename: "/lib/python3.15/__pycache__/rlcompleter.cpython-315.pyc",
        start: 1258680,
        end: 1267486
      }, {
        filename: "/lib/python3.15/__pycache__/selectors.cpython-315.pyc",
        start: 1267486,
        end: 1294636
      }, {
        filename: "/lib/python3.15/__pycache__/shutil.cpython-315.pyc",
        start: 1294636,
        end: 1367387
      }, {
        filename: "/lib/python3.15/__pycache__/signal.cpython-315.pyc",
        start: 1367387,
        end: 1371976
      }, {
        filename: "/lib/python3.15/__pycache__/site.cpython-315.pyc",
        start: 1371976,
        end: 1404577
      }, {
        filename: "/lib/python3.15/__pycache__/socket.cpython-315.pyc",
        start: 1404577,
        end: 1448159
      }, {
        filename: "/lib/python3.15/__pycache__/ssl.cpython-315.pyc",
        start: 1448159,
        end: 1516654
      }, {
        filename: "/lib/python3.15/__pycache__/stat.cpython-315.pyc",
        start: 1516654,
        end: 1522483
      }, {
        filename: "/lib/python3.15/__pycache__/struct.cpython-315.pyc",
        start: 1522483,
        end: 1522808
      }, {
        filename: "/lib/python3.15/__pycache__/subprocess.cpython-315.pyc",
        start: 1522808,
        end: 1608542
      }, {
        filename: "/lib/python3.15/__pycache__/textwrap.cpython-315.pyc",
        start: 1608542,
        end: 1626988
      }, {
        filename: "/lib/python3.15/__pycache__/threading.cpython-315.pyc",
        start: 1626988,
        end: 1693571
      }, {
        filename: "/lib/python3.15/__pycache__/token.cpython-315.pyc",
        start: 1693571,
        end: 1697443
      }, {
        filename: "/lib/python3.15/__pycache__/tokenize.cpython-315.pyc",
        start: 1697443,
        end: 1724461
      }, {
        filename: "/lib/python3.15/__pycache__/traceback.cpython-315.pyc",
        start: 1724461,
        end: 1806767
      }, {
        filename: "/lib/python3.15/__pycache__/types.cpython-315.pyc",
        start: 1806767,
        end: 1822581
      }, {
        filename: "/lib/python3.15/__pycache__/typing.cpython-315.pyc",
        start: 1822581,
        end: 1993644
      }, {
        filename: "/lib/python3.15/__pycache__/warnings.cpython-315.pyc",
        start: 1993644,
        end: 1996144
      }, {
        filename: "/lib/python3.15/__pycache__/weakref.cpython-315.pyc",
        start: 1996144,
        end: 2023813
      }, {
        filename: "/lib/python3.15/_aix_support.py",
        start: 2023813,
        end: 2027834
      }, {
        filename: "/lib/python3.15/_android_support.py",
        start: 2027834,
        end: 2034899
      }, {
        filename: "/lib/python3.15/_apple_support.py",
        start: 2034899,
        end: 2037155
      }, {
        filename: "/lib/python3.15/_ast_unparse.py",
        start: 2037155,
        end: 2077577
      }, {
        filename: "/lib/python3.15/_collections_abc.py",
        start: 2077577,
        end: 2110033
      }, {
        filename: "/lib/python3.15/_colorize.py",
        start: 2110033,
        end: 2121902
      }, {
        filename: "/lib/python3.15/_compat_pickle.py",
        start: 2121902,
        end: 2130503
      }, {
        filename: "/lib/python3.15/_ios_support.py",
        start: 2130503,
        end: 2133175
      }, {
        filename: "/lib/python3.15/_markupbase.py",
        start: 2133175,
        end: 2147870
      }, {
        filename: "/lib/python3.15/_opcode_metadata.py",
        start: 2147870,
        end: 2157861
      }, {
        filename: "/lib/python3.15/_osx_support.py",
        start: 2157861,
        end: 2179884
      }, {
        filename: "/lib/python3.15/_py_abc.py",
        start: 2179884,
        end: 2186073
      }, {
        filename: "/lib/python3.15/_py_warnings.py",
        start: 2186073,
        end: 2218780
      }, {
        filename: "/lib/python3.15/_pydatetime.py",
        start: 2218780,
        end: 2316056
      }, {
        filename: "/lib/python3.15/_pydecimal.py",
        start: 2316056,
        end: 2545680
      }, {
        filename: "/lib/python3.15/_pyio.py",
        start: 2545680,
        end: 2642324
      }, {
        filename: "/lib/python3.15/_pylong.py",
        start: 2642324,
        end: 2670680
      }, {
        filename: "/lib/python3.15/_pyrepl/__init__.py",
        start: 2670680,
        end: 2671605
      }, {
        filename: "/lib/python3.15/_pyrepl/__main__.py",
        start: 2671605,
        end: 2672027
      }, {
        filename: "/lib/python3.15/_pyrepl/__pycache__/__init__.cpython-315.pyc",
        start: 2672027,
        end: 2672163
      }, {
        filename: "/lib/python3.15/_pyrepl/__pycache__/commands.cpython-315.pyc",
        start: 2672163,
        end: 2705184
      }, {
        filename: "/lib/python3.15/_pyrepl/__pycache__/historical_reader.cpython-315.pyc",
        start: 2705184,
        end: 2731427
      }, {
        filename: "/lib/python3.15/_pyrepl/__pycache__/input.cpython-315.pyc",
        start: 2731427,
        end: 2736052
      }, {
        filename: "/lib/python3.15/_pyrepl/__pycache__/main.cpython-315.pyc",
        start: 2736052,
        end: 2739167
      }, {
        filename: "/lib/python3.15/_pyrepl/__pycache__/readline.cpython-315.pyc",
        start: 2739167,
        end: 2774053
      }, {
        filename: "/lib/python3.15/_pyrepl/__pycache__/simple_interact.cpython-315.pyc",
        start: 2774053,
        end: 2782578
      }, {
        filename: "/lib/python3.15/_pyrepl/__pycache__/trace.cpython-315.pyc",
        start: 2782578,
        end: 2784294
      }, {
        filename: "/lib/python3.15/_pyrepl/_module_completer.py",
        start: 2784294,
        end: 2799014
      }, {
        filename: "/lib/python3.15/_pyrepl/_threading_handler.py",
        start: 2799014,
        end: 2801184
      }, {
        filename: "/lib/python3.15/_pyrepl/base_eventqueue.py",
        start: 2801184,
        end: 2805024
      }, {
        filename: "/lib/python3.15/_pyrepl/commands.py",
        start: 2805024,
        end: 2817749
      }, {
        filename: "/lib/python3.15/_pyrepl/completing_reader.py",
        start: 2817749,
        end: 2827944
      }, {
        filename: "/lib/python3.15/_pyrepl/console.py",
        start: 2827944,
        end: 2835428
      }, {
        filename: "/lib/python3.15/_pyrepl/fancy_termios.py",
        start: 2835428,
        end: 2837994
      }, {
        filename: "/lib/python3.15/_pyrepl/historical_reader.py",
        start: 2837994,
        end: 2851234
      }, {
        filename: "/lib/python3.15/_pyrepl/input.py",
        start: 2851234,
        end: 2855013
      }, {
        filename: "/lib/python3.15/_pyrepl/keymap.py",
        start: 2855013,
        end: 2861473
      }, {
        filename: "/lib/python3.15/_pyrepl/main.py",
        start: 2861473,
        end: 2863343
      }, {
        filename: "/lib/python3.15/_pyrepl/mypy.ini",
        start: 2863343,
        end: 2864129
      }, {
        filename: "/lib/python3.15/_pyrepl/pager.py",
        start: 2864129,
        end: 2869944
      }, {
        filename: "/lib/python3.15/_pyrepl/reader.py",
        start: 2869944,
        end: 2897533
      }, {
        filename: "/lib/python3.15/_pyrepl/readline.py",
        start: 2897533,
        end: 2918947
      }, {
        filename: "/lib/python3.15/_pyrepl/simple_interact.py",
        start: 2918947,
        end: 2924884
      }, {
        filename: "/lib/python3.15/_pyrepl/terminfo.py",
        start: 2924884,
        end: 2943334
      }, {
        filename: "/lib/python3.15/_pyrepl/trace.py",
        start: 2943334,
        end: 2944101
      }, {
        filename: "/lib/python3.15/_pyrepl/types.py",
        start: 2944101,
        end: 2944455
      }, {
        filename: "/lib/python3.15/_pyrepl/unix_console.py",
        start: 2944455,
        end: 2970880
      }, {
        filename: "/lib/python3.15/_pyrepl/unix_eventqueue.py",
        start: 2970880,
        end: 2973434
      }, {
        filename: "/lib/python3.15/_pyrepl/utils.py",
        start: 2973434,
        end: 2986556
      }, {
        filename: "/lib/python3.15/_pyrepl/windows_console.py",
        start: 2986556,
        end: 3008968
      }, {
        filename: "/lib/python3.15/_pyrepl/windows_eventqueue.py",
        start: 3008968,
        end: 3009959
      }, {
        filename: "/lib/python3.15/_sitebuiltins.py",
        start: 3009959,
        end: 3013087
      }, {
        filename: "/lib/python3.15/_strptime.py",
        start: 3013087,
        end: 3049204
      }, {
        filename: "/lib/python3.15/_threading_local.py",
        start: 3049204,
        end: 3053561
      }, {
        filename: "/lib/python3.15/_weakrefset.py",
        start: 3053561,
        end: 3057523
      }, {
        filename: "/lib/python3.15/abc.py",
        start: 3057523,
        end: 3064061
      }, {
        filename: "/lib/python3.15/annotationlib.py",
        start: 3064061,
        end: 3106095
      }, {
        filename: "/lib/python3.15/antigravity.py",
        start: 3106095,
        end: 3106595
      }, {
        filename: "/lib/python3.15/argparse.py",
        start: 3106595,
        end: 3217254
      }, {
        filename: "/lib/python3.15/ast.py",
        start: 3217254,
        end: 3242921
      }, {
        filename: "/lib/python3.15/asyncio/__init__.py",
        start: 3242921,
        end: 3245334
      }, {
        filename: "/lib/python3.15/asyncio/__main__.py",
        start: 3245334,
        end: 3252954
      }, {
        filename: "/lib/python3.15/asyncio/__pycache__/__init__.cpython-315.pyc",
        start: 3252954,
        end: 3256079
      }, {
        filename: "/lib/python3.15/asyncio/__pycache__/base_events.cpython-315.pyc",
        start: 3256079,
        end: 3348967
      }, {
        filename: "/lib/python3.15/asyncio/__pycache__/base_futures.cpython-315.pyc",
        start: 3348967,
        end: 3352201
      }, {
        filename: "/lib/python3.15/asyncio/__pycache__/base_subprocess.cpython-315.pyc",
        start: 3352201,
        end: 3370380
      }, {
        filename: "/lib/python3.15/asyncio/__pycache__/base_tasks.cpython-315.pyc",
        start: 3370380,
        end: 3374584
      }, {
        filename: "/lib/python3.15/asyncio/__pycache__/constants.cpython-315.pyc",
        start: 3374584,
        end: 3375573
      }, {
        filename: "/lib/python3.15/asyncio/__pycache__/coroutines.cpython-315.pyc",
        start: 3375573,
        end: 3380050
      }, {
        filename: "/lib/python3.15/asyncio/__pycache__/events.cpython-315.pyc",
        start: 3380050,
        end: 3417855
      }, {
        filename: "/lib/python3.15/asyncio/__pycache__/exceptions.cpython-315.pyc",
        start: 3417855,
        end: 3421118
      }, {
        filename: "/lib/python3.15/asyncio/__pycache__/format_helpers.cpython-315.pyc",
        start: 3421118,
        end: 3425448
      }, {
        filename: "/lib/python3.15/asyncio/__pycache__/futures.cpython-315.pyc",
        start: 3425448,
        end: 3444578
      }, {
        filename: "/lib/python3.15/asyncio/__pycache__/graph.cpython-315.pyc",
        start: 3444578,
        end: 3455924
      }, {
        filename: "/lib/python3.15/asyncio/__pycache__/locks.cpython-315.pyc",
        start: 3455924,
        end: 3484800
      }, {
        filename: "/lib/python3.15/asyncio/__pycache__/log.cpython-315.pyc",
        start: 3484800,
        end: 3485074
      }, {
        filename: "/lib/python3.15/asyncio/__pycache__/mixins.cpython-315.pyc",
        start: 3485074,
        end: 3486249
      }, {
        filename: "/lib/python3.15/asyncio/__pycache__/protocols.cpython-315.pyc",
        start: 3486249,
        end: 3494804
      }, {
        filename: "/lib/python3.15/asyncio/__pycache__/queues.cpython-315.pyc",
        start: 3494804,
        end: 3509576
      }, {
        filename: "/lib/python3.15/asyncio/__pycache__/runners.cpython-315.pyc",
        start: 3509576,
        end: 3520289
      }, {
        filename: "/lib/python3.15/asyncio/__pycache__/selector_events.cpython-315.pyc",
        start: 3520289,
        end: 3587214
      }, {
        filename: "/lib/python3.15/asyncio/__pycache__/sslproto.cpython-315.pyc",
        start: 3587214,
        end: 3629936
      }, {
        filename: "/lib/python3.15/asyncio/__pycache__/staggered.cpython-315.pyc",
        start: 3629936,
        end: 3637172
      }, {
        filename: "/lib/python3.15/asyncio/__pycache__/streams.cpython-315.pyc",
        start: 3637172,
        end: 3671589
      }, {
        filename: "/lib/python3.15/asyncio/__pycache__/subprocess.cpython-315.pyc",
        start: 3671589,
        end: 3684208
      }, {
        filename: "/lib/python3.15/asyncio/__pycache__/taskgroups.cpython-315.pyc",
        start: 3684208,
        end: 3693995
      }, {
        filename: "/lib/python3.15/asyncio/__pycache__/tasks.cpython-315.pyc",
        start: 3693995,
        end: 3739903
      }, {
        filename: "/lib/python3.15/asyncio/__pycache__/threads.cpython-315.pyc",
        start: 3739903,
        end: 3741132
      }, {
        filename: "/lib/python3.15/asyncio/__pycache__/timeouts.cpython-315.pyc",
        start: 3741132,
        end: 3751558
      }, {
        filename: "/lib/python3.15/asyncio/__pycache__/transports.cpython-315.pyc",
        start: 3751558,
        end: 3765560
      }, {
        filename: "/lib/python3.15/asyncio/__pycache__/trsock.cpython-315.pyc",
        start: 3765560,
        end: 3770981
      }, {
        filename: "/lib/python3.15/asyncio/__pycache__/unix_events.cpython-315.pyc",
        start: 3770981,
        end: 3819313
      }, {
        filename: "/lib/python3.15/asyncio/base_events.py",
        start: 3819313,
        end: 3899982
      }, {
        filename: "/lib/python3.15/asyncio/base_futures.py",
        start: 3899982,
        end: 3901956
      }, {
        filename: "/lib/python3.15/asyncio/base_subprocess.py",
        start: 3901956,
        end: 3912295
      }, {
        filename: "/lib/python3.15/asyncio/base_tasks.py",
        start: 3912295,
        end: 3914967
      }, {
        filename: "/lib/python3.15/asyncio/constants.py",
        start: 3914967,
        end: 3916380
      }, {
        filename: "/lib/python3.15/asyncio/coroutines.py",
        start: 3916380,
        end: 3920037
      }, {
        filename: "/lib/python3.15/asyncio/events.py",
        start: 3920037,
        end: 3949568
      }, {
        filename: "/lib/python3.15/asyncio/exceptions.py",
        start: 3949568,
        end: 3951320
      }, {
        filename: "/lib/python3.15/asyncio/format_helpers.py",
        start: 3951320,
        end: 3954047
      }, {
        filename: "/lib/python3.15/asyncio/futures.py",
        start: 3954047,
        end: 3970849
      }, {
        filename: "/lib/python3.15/asyncio/graph.py",
        start: 3970849,
        end: 3979523
      }, {
        filename: "/lib/python3.15/asyncio/locks.py",
        start: 3979523,
        end: 4000097
      }, {
        filename: "/lib/python3.15/asyncio/log.py",
        start: 4000097,
        end: 4000221
      }, {
        filename: "/lib/python3.15/asyncio/mixins.py",
        start: 4000221,
        end: 4000702
      }, {
        filename: "/lib/python3.15/asyncio/proactor_events.py",
        start: 4000702,
        end: 4034224
      }, {
        filename: "/lib/python3.15/asyncio/protocols.py",
        start: 4034224,
        end: 4041181
      }, {
        filename: "/lib/python3.15/asyncio/queues.py",
        start: 4041181,
        end: 4051333
      }, {
        filename: "/lib/python3.15/asyncio/runners.py",
        start: 4051333,
        end: 4058820
      }, {
        filename: "/lib/python3.15/asyncio/selector_events.py",
        start: 4058820,
        end: 4107443
      }, {
        filename: "/lib/python3.15/asyncio/sslproto.py",
        start: 4107443,
        end: 4139312
      }, {
        filename: "/lib/python3.15/asyncio/staggered.py",
        start: 4139312,
        end: 4146583
      }, {
        filename: "/lib/python3.15/asyncio/streams.py",
        start: 4146583,
        end: 4174657
      }, {
        filename: "/lib/python3.15/asyncio/subprocess.py",
        start: 4174657,
        end: 4182394
      }, {
        filename: "/lib/python3.15/asyncio/taskgroups.py",
        start: 4182394,
        end: 4192464
      }, {
        filename: "/lib/python3.15/asyncio/tasks.py",
        start: 4192464,
        end: 4232922
      }, {
        filename: "/lib/python3.15/asyncio/threads.py",
        start: 4232922,
        end: 4233712
      }, {
        filename: "/lib/python3.15/asyncio/timeouts.py",
        start: 4233712,
        end: 4239693
      }, {
        filename: "/lib/python3.15/asyncio/tools.py",
        start: 4239693,
        end: 4249599
      }, {
        filename: "/lib/python3.15/asyncio/transports.py",
        start: 4249599,
        end: 4260407
      }, {
        filename: "/lib/python3.15/asyncio/trsock.py",
        start: 4260407,
        end: 4262882
      }, {
        filename: "/lib/python3.15/asyncio/unix_events.py",
        start: 4262882,
        end: 4298395
      }, {
        filename: "/lib/python3.15/asyncio/windows_events.py",
        start: 4298395,
        end: 4331034
      }, {
        filename: "/lib/python3.15/asyncio/windows_utils.py",
        start: 4331034,
        end: 4336094
      }, {
        filename: "/lib/python3.15/base64.py",
        start: 4336094,
        end: 4358135
      }, {
        filename: "/lib/python3.15/bdb.py",
        start: 4358135,
        end: 4402516
      }, {
        filename: "/lib/python3.15/bisect.py",
        start: 4402516,
        end: 4405939
      }, {
        filename: "/lib/python3.15/bz2.py",
        start: 4405939,
        end: 4417917
      }, {
        filename: "/lib/python3.15/cProfile.py",
        start: 4417917,
        end: 4418244
      }, {
        filename: "/lib/python3.15/calendar.py",
        start: 4418244,
        end: 4449487
      }, {
        filename: "/lib/python3.15/cmd.py",
        start: 4449487,
        end: 4464898
      }, {
        filename: "/lib/python3.15/code.py",
        start: 4464898,
        end: 4478334
      }, {
        filename: "/lib/python3.15/codecs.py",
        start: 4478334,
        end: 4515174
      }, {
        filename: "/lib/python3.15/codeop.py",
        start: 4515174,
        end: 4521066
      }, {
        filename: "/lib/python3.15/collections/__init__.py",
        start: 4521066,
        end: 4575410
      }, {
        filename: "/lib/python3.15/collections/__pycache__/__init__.cpython-315.pyc",
        start: 4575410,
        end: 4651819
      }, {
        filename: "/lib/python3.15/colorsys.py",
        start: 4651819,
        end: 4655881
      }, {
        filename: "/lib/python3.15/compileall.py",
        start: 4655881,
        end: 4676555
      }, {
        filename: "/lib/python3.15/compression/__init__.py",
        start: 4676555,
        end: 4676555
      }, {
        filename: "/lib/python3.15/compression/__pycache__/__init__.cpython-315.pyc",
        start: 4676555,
        end: 4676695
      }, {
        filename: "/lib/python3.15/compression/_common/__init__.py",
        start: 4676695,
        end: 4676695
      }, {
        filename: "/lib/python3.15/compression/_common/__pycache__/__init__.cpython-315.pyc",
        start: 4676695,
        end: 4676843
      }, {
        filename: "/lib/python3.15/compression/_common/__pycache__/_streams.cpython-315.pyc",
        start: 4676843,
        end: 4684662
      }, {
        filename: "/lib/python3.15/compression/_common/_streams.py",
        start: 4684662,
        end: 4690332
      }, {
        filename: "/lib/python3.15/compression/bz2.py",
        start: 4690332,
        end: 4690392
      }, {
        filename: "/lib/python3.15/compression/gzip.py",
        start: 4690392,
        end: 4690456
      }, {
        filename: "/lib/python3.15/compression/lzma.py",
        start: 4690456,
        end: 4690520
      }, {
        filename: "/lib/python3.15/compression/zlib.py",
        start: 4690520,
        end: 4690584
      }, {
        filename: "/lib/python3.15/compression/zstd/__init__.py",
        start: 4690584,
        end: 4699343
      }, {
        filename: "/lib/python3.15/compression/zstd/__pycache__/__init__.cpython-315.pyc",
        start: 4699343,
        end: 4711062
      }, {
        filename: "/lib/python3.15/compression/zstd/__pycache__/_zstdfile.cpython-315.pyc",
        start: 4711062,
        end: 4726823
      }, {
        filename: "/lib/python3.15/compression/zstd/_zstdfile.py",
        start: 4726823,
        end: 4739109
      }, {
        filename: "/lib/python3.15/concurrent/__init__.py",
        start: 4739109,
        end: 4739147
      }, {
        filename: "/lib/python3.15/concurrent/__pycache__/__init__.cpython-315.pyc",
        start: 4739147,
        end: 4739286
      }, {
        filename: "/lib/python3.15/concurrent/futures/__init__.py",
        start: 4739286,
        end: 4741149
      }, {
        filename: "/lib/python3.15/concurrent/futures/__pycache__/__init__.cpython-315.pyc",
        start: 4741149,
        end: 4742751
      }, {
        filename: "/lib/python3.15/concurrent/futures/__pycache__/_base.cpython-315.pyc",
        start: 4742751,
        end: 4778750
      }, {
        filename: "/lib/python3.15/concurrent/futures/_base.py",
        start: 4778750,
        end: 4804065
      }, {
        filename: "/lib/python3.15/concurrent/futures/interpreter.py",
        start: 4804065,
        end: 4808089
      }, {
        filename: "/lib/python3.15/concurrent/futures/process.py",
        start: 4808089,
        end: 4847073
      }, {
        filename: "/lib/python3.15/concurrent/futures/thread.py",
        start: 4847073,
        end: 4856906
      }, {
        filename: "/lib/python3.15/concurrent/interpreters/__init__.py",
        start: 4856906,
        end: 4864613
      }, {
        filename: "/lib/python3.15/concurrent/interpreters/_crossinterp.py",
        start: 4864613,
        end: 4867520
      }, {
        filename: "/lib/python3.15/concurrent/interpreters/_queues.py",
        start: 4867520,
        end: 4876166
      }, {
        filename: "/lib/python3.15/configparser.py",
        start: 4876166,
        end: 4931294
      }, {
        filename: "/lib/python3.15/contextlib.py",
        start: 4931294,
        end: 4959095
      }, {
        filename: "/lib/python3.15/contextvars.py",
        start: 4959095,
        end: 4959293
      }, {
        filename: "/lib/python3.15/copy.py",
        start: 4959293,
        end: 4967898
      }, {
        filename: "/lib/python3.15/copyreg.py",
        start: 4967898,
        end: 4975614
      }, {
        filename: "/lib/python3.15/csv.py",
        start: 4975614,
        end: 4995176
      }, {
        filename: "/lib/python3.15/ctypes/__init__.py",
        start: 4995176,
        end: 5017170
      }, {
        filename: "/lib/python3.15/ctypes/_aix.py",
        start: 5017170,
        end: 5029675
      }, {
        filename: "/lib/python3.15/ctypes/_endian.py",
        start: 5029675,
        end: 5032232
      }, {
        filename: "/lib/python3.15/ctypes/_layout.py",
        start: 5032232,
        end: 5043674
      }, {
        filename: "/lib/python3.15/ctypes/macholib/README.ctypes",
        start: 5043674,
        end: 5043970
      }, {
        filename: "/lib/python3.15/ctypes/macholib/__init__.py",
        start: 5043970,
        end: 5044363
      }, {
        filename: "/lib/python3.15/ctypes/macholib/dyld.py",
        start: 5044363,
        end: 5049387
      }, {
        filename: "/lib/python3.15/ctypes/macholib/dylib.py",
        start: 5049387,
        end: 5050347
      }, {
        filename: "/lib/python3.15/ctypes/macholib/fetch_macholib",
        start: 5050347,
        end: 5050431
      }, {
        filename: "/lib/python3.15/ctypes/macholib/fetch_macholib.bat",
        start: 5050431,
        end: 5050506
      }, {
        filename: "/lib/python3.15/ctypes/macholib/framework.py",
        start: 5050506,
        end: 5051611
      }, {
        filename: "/lib/python3.15/ctypes/util.py",
        start: 5051611,
        end: 5071452
      }, {
        filename: "/lib/python3.15/ctypes/wintypes.py",
        start: 5071452,
        end: 5077205
      }, {
        filename: "/lib/python3.15/curses/__init__.py",
        start: 5077205,
        end: 5080568
      }, {
        filename: "/lib/python3.15/curses/ascii.py",
        start: 5080568,
        end: 5083111
      }, {
        filename: "/lib/python3.15/curses/has_key.py",
        start: 5083111,
        end: 5088745
      }, {
        filename: "/lib/python3.15/curses/panel.py",
        start: 5088745,
        end: 5088832
      }, {
        filename: "/lib/python3.15/curses/textpad.py",
        start: 5088832,
        end: 5096586
      }, {
        filename: "/lib/python3.15/dataclasses.py",
        start: 5096586,
        end: 5167960
      }, {
        filename: "/lib/python3.15/datetime.py",
        start: 5167960,
        end: 5168291
      }, {
        filename: "/lib/python3.15/dbm/__init__.py",
        start: 5168291,
        end: 5174315
      }, {
        filename: "/lib/python3.15/dbm/dumb.py",
        start: 5174315,
        end: 5187020
      }, {
        filename: "/lib/python3.15/dbm/gnu.py",
        start: 5187020,
        end: 5187092
      }, {
        filename: "/lib/python3.15/dbm/ndbm.py",
        start: 5187092,
        end: 5187162
      }, {
        filename: "/lib/python3.15/dbm/sqlite3.py",
        start: 5187162,
        end: 5191518
      }, {
        filename: "/lib/python3.15/decimal.py",
        start: 5191518,
        end: 5194344
      }, {
        filename: "/lib/python3.15/difflib.py",
        start: 5194344,
        end: 5279474
      }, {
        filename: "/lib/python3.15/dis.py",
        start: 5279474,
        end: 5324973
      }, {
        filename: "/lib/python3.15/doctest.py",
        start: 5324973,
        end: 5437845
      }, {
        filename: "/lib/python3.15/email/__init__.py",
        start: 5437845,
        end: 5439604
      }, {
        filename: "/lib/python3.15/email/_encoded_words.py",
        start: 5439604,
        end: 5448145
      }, {
        filename: "/lib/python3.15/email/_header_value_parser.py",
        start: 5448145,
        end: 5560895
      }, {
        filename: "/lib/python3.15/email/_parseaddr.py",
        start: 5560895,
        end: 5579015
      }, {
        filename: "/lib/python3.15/email/_policybase.py",
        start: 5579015,
        end: 5594975
      }, {
        filename: "/lib/python3.15/email/architecture.rst",
        start: 5594975,
        end: 5604536
      }, {
        filename: "/lib/python3.15/email/base64mime.py",
        start: 5604536,
        end: 5608082
      }, {
        filename: "/lib/python3.15/email/charset.py",
        start: 5608082,
        end: 5625140
      }, {
        filename: "/lib/python3.15/email/contentmanager.py",
        start: 5625140,
        end: 5635734
      }, {
        filename: "/lib/python3.15/email/encoders.py",
        start: 5635734,
        end: 5637507
      }, {
        filename: "/lib/python3.15/email/errors.py",
        start: 5637507,
        end: 5641316
      }, {
        filename: "/lib/python3.15/email/feedparser.py",
        start: 5641316,
        end: 5664180
      }, {
        filename: "/lib/python3.15/email/generator.py",
        start: 5664180,
        end: 5684992
      }, {
        filename: "/lib/python3.15/email/header.py",
        start: 5684992,
        end: 5709451
      }, {
        filename: "/lib/python3.15/email/headerregistry.py",
        start: 5709451,
        end: 5730695
      }, {
        filename: "/lib/python3.15/email/iterators.py",
        start: 5730695,
        end: 5732819
      }, {
        filename: "/lib/python3.15/email/message.py",
        start: 5732819,
        end: 5781256
      }, {
        filename: "/lib/python3.15/email/mime/__init__.py",
        start: 5781256,
        end: 5781256
      }, {
        filename: "/lib/python3.15/email/mime/application.py",
        start: 5781256,
        end: 5782572
      }, {
        filename: "/lib/python3.15/email/mime/audio.py",
        start: 5782572,
        end: 5785571
      }, {
        filename: "/lib/python3.15/email/mime/base.py",
        start: 5785571,
        end: 5786480
      }, {
        filename: "/lib/python3.15/email/mime/image.py",
        start: 5786480,
        end: 5790201
      }, {
        filename: "/lib/python3.15/email/mime/message.py",
        start: 5790201,
        end: 5791511
      }, {
        filename: "/lib/python3.15/email/mime/multipart.py",
        start: 5791511,
        end: 5793125
      }, {
        filename: "/lib/python3.15/email/mime/nonmultipart.py",
        start: 5793125,
        end: 5793809
      }, {
        filename: "/lib/python3.15/email/mime/text.py",
        start: 5793809,
        end: 5795198
      }, {
        filename: "/lib/python3.15/email/parser.py",
        start: 5795198,
        end: 5800168
      }, {
        filename: "/lib/python3.15/email/policy.py",
        start: 5800168,
        end: 5810863
      }, {
        filename: "/lib/python3.15/email/quoprimime.py",
        start: 5810863,
        end: 5820722
      }, {
        filename: "/lib/python3.15/email/utils.py",
        start: 5820722,
        end: 5837187
      }, {
        filename: "/lib/python3.15/encodings/__init__.py",
        start: 5837187,
        end: 5842967
      }, {
        filename: "/lib/python3.15/encodings/__pycache__/__init__.cpython-315.pyc",
        start: 5842967,
        end: 5849398
      }, {
        filename: "/lib/python3.15/encodings/__pycache__/aliases.cpython-315.pyc",
        start: 5849398,
        end: 5862381
      }, {
        filename: "/lib/python3.15/encodings/__pycache__/utf_8.cpython-315.pyc",
        start: 5862381,
        end: 5864709
      }, {
        filename: "/lib/python3.15/encodings/_win_cp_codecs.py",
        start: 5864709,
        end: 5865938
      }, {
        filename: "/lib/python3.15/encodings/aliases.py",
        start: 5865938,
        end: 5882322
      }, {
        filename: "/lib/python3.15/encodings/ascii.py",
        start: 5882322,
        end: 5883570
      }, {
        filename: "/lib/python3.15/encodings/base64_codec.py",
        start: 5883570,
        end: 5885103
      }, {
        filename: "/lib/python3.15/encodings/big5.py",
        start: 5885103,
        end: 5886122
      }, {
        filename: "/lib/python3.15/encodings/big5hkscs.py",
        start: 5886122,
        end: 5887161
      }, {
        filename: "/lib/python3.15/encodings/bz2_codec.py",
        start: 5887161,
        end: 5889410
      }, {
        filename: "/lib/python3.15/encodings/charmap.py",
        start: 5889410,
        end: 5891494
      }, {
        filename: "/lib/python3.15/encodings/cp037.py",
        start: 5891494,
        end: 5904615
      }, {
        filename: "/lib/python3.15/encodings/cp1006.py",
        start: 5904615,
        end: 5918183
      }, {
        filename: "/lib/python3.15/encodings/cp1026.py",
        start: 5918183,
        end: 5931296
      }, {
        filename: "/lib/python3.15/encodings/cp1125.py",
        start: 5931296,
        end: 5965893
      }, {
        filename: "/lib/python3.15/encodings/cp1140.py",
        start: 5965893,
        end: 5978998
      }, {
        filename: "/lib/python3.15/encodings/cp1250.py",
        start: 5978998,
        end: 5992684
      }, {
        filename: "/lib/python3.15/encodings/cp1251.py",
        start: 5992684,
        end: 6006045
      }, {
        filename: "/lib/python3.15/encodings/cp1252.py",
        start: 6006045,
        end: 6019556
      }, {
        filename: "/lib/python3.15/encodings/cp1253.py",
        start: 6019556,
        end: 6032650
      }, {
        filename: "/lib/python3.15/encodings/cp1254.py",
        start: 6032650,
        end: 6046152
      }, {
        filename: "/lib/python3.15/encodings/cp1255.py",
        start: 6046152,
        end: 6058618
      }, {
        filename: "/lib/python3.15/encodings/cp1256.py",
        start: 6058618,
        end: 6071432
      }, {
        filename: "/lib/python3.15/encodings/cp1257.py",
        start: 6071432,
        end: 6084806
      }, {
        filename: "/lib/python3.15/encodings/cp1258.py",
        start: 6084806,
        end: 6098170
      }, {
        filename: "/lib/python3.15/encodings/cp273.py",
        start: 6098170,
        end: 6112302
      }, {
        filename: "/lib/python3.15/encodings/cp424.py",
        start: 6112302,
        end: 6124357
      }, {
        filename: "/lib/python3.15/encodings/cp437.py",
        start: 6124357,
        end: 6158921
      }, {
        filename: "/lib/python3.15/encodings/cp500.py",
        start: 6158921,
        end: 6172042
      }, {
        filename: "/lib/python3.15/encodings/cp720.py",
        start: 6172042,
        end: 6185728
      }, {
        filename: "/lib/python3.15/encodings/cp737.py",
        start: 6185728,
        end: 6220409
      }, {
        filename: "/lib/python3.15/encodings/cp775.py",
        start: 6220409,
        end: 6254885
      }, {
        filename: "/lib/python3.15/encodings/cp850.py",
        start: 6254885,
        end: 6288990
      }, {
        filename: "/lib/python3.15/encodings/cp852.py",
        start: 6288990,
        end: 6323992
      }, {
        filename: "/lib/python3.15/encodings/cp855.py",
        start: 6323992,
        end: 6357842
      }, {
        filename: "/lib/python3.15/encodings/cp856.py",
        start: 6357842,
        end: 6370265
      }, {
        filename: "/lib/python3.15/encodings/cp857.py",
        start: 6370265,
        end: 6404173
      }, {
        filename: "/lib/python3.15/encodings/cp858.py",
        start: 6404173,
        end: 6438188
      }, {
        filename: "/lib/python3.15/encodings/cp860.py",
        start: 6438188,
        end: 6472869
      }, {
        filename: "/lib/python3.15/encodings/cp861.py",
        start: 6472869,
        end: 6507502
      }, {
        filename: "/lib/python3.15/encodings/cp862.py",
        start: 6507502,
        end: 6540872
      }, {
        filename: "/lib/python3.15/encodings/cp863.py",
        start: 6540872,
        end: 6575124
      }, {
        filename: "/lib/python3.15/encodings/cp864.py",
        start: 6575124,
        end: 6608787
      }, {
        filename: "/lib/python3.15/encodings/cp865.py",
        start: 6608787,
        end: 6643405
      }, {
        filename: "/lib/python3.15/encodings/cp866.py",
        start: 6643405,
        end: 6677801
      }, {
        filename: "/lib/python3.15/encodings/cp869.py",
        start: 6677801,
        end: 6710766
      }, {
        filename: "/lib/python3.15/encodings/cp874.py",
        start: 6710766,
        end: 6723361
      }, {
        filename: "/lib/python3.15/encodings/cp875.py",
        start: 6723361,
        end: 6736215
      }, {
        filename: "/lib/python3.15/encodings/cp932.py",
        start: 6736215,
        end: 6737238
      }, {
        filename: "/lib/python3.15/encodings/cp949.py",
        start: 6737238,
        end: 6738261
      }, {
        filename: "/lib/python3.15/encodings/cp950.py",
        start: 6738261,
        end: 6739284
      }, {
        filename: "/lib/python3.15/encodings/euc_jis_2004.py",
        start: 6739284,
        end: 6740335
      }, {
        filename: "/lib/python3.15/encodings/euc_jisx0213.py",
        start: 6740335,
        end: 6741386
      }, {
        filename: "/lib/python3.15/encodings/euc_jp.py",
        start: 6741386,
        end: 6742413
      }, {
        filename: "/lib/python3.15/encodings/euc_kr.py",
        start: 6742413,
        end: 6743440
      }, {
        filename: "/lib/python3.15/encodings/gb18030.py",
        start: 6743440,
        end: 6744471
      }, {
        filename: "/lib/python3.15/encodings/gb2312.py",
        start: 6744471,
        end: 6745498
      }, {
        filename: "/lib/python3.15/encodings/gbk.py",
        start: 6745498,
        end: 6746513
      }, {
        filename: "/lib/python3.15/encodings/hex_codec.py",
        start: 6746513,
        end: 6748021
      }, {
        filename: "/lib/python3.15/encodings/hp_roman8.py",
        start: 6748021,
        end: 6761496
      }, {
        filename: "/lib/python3.15/encodings/hz.py",
        start: 6761496,
        end: 6762507
      }, {
        filename: "/lib/python3.15/encodings/idna.py",
        start: 6762507,
        end: 6775785
      }, {
        filename: "/lib/python3.15/encodings/iso2022_jp.py",
        start: 6775785,
        end: 6776838
      }, {
        filename: "/lib/python3.15/encodings/iso2022_jp_1.py",
        start: 6776838,
        end: 6777899
      }, {
        filename: "/lib/python3.15/encodings/iso2022_jp_2.py",
        start: 6777899,
        end: 6778960
      }, {
        filename: "/lib/python3.15/encodings/iso2022_jp_2004.py",
        start: 6778960,
        end: 6780033
      }, {
        filename: "/lib/python3.15/encodings/iso2022_jp_3.py",
        start: 6780033,
        end: 6781094
      }, {
        filename: "/lib/python3.15/encodings/iso2022_jp_ext.py",
        start: 6781094,
        end: 6782163
      }, {
        filename: "/lib/python3.15/encodings/iso2022_kr.py",
        start: 6782163,
        end: 6783216
      }, {
        filename: "/lib/python3.15/encodings/iso8859_1.py",
        start: 6783216,
        end: 6796392
      }, {
        filename: "/lib/python3.15/encodings/iso8859_10.py",
        start: 6796392,
        end: 6809981
      }, {
        filename: "/lib/python3.15/encodings/iso8859_11.py",
        start: 6809981,
        end: 6822316
      }, {
        filename: "/lib/python3.15/encodings/iso8859_13.py",
        start: 6822316,
        end: 6835587
      }, {
        filename: "/lib/python3.15/encodings/iso8859_14.py",
        start: 6835587,
        end: 6849239
      }, {
        filename: "/lib/python3.15/encodings/iso8859_15.py",
        start: 6849239,
        end: 6862451
      }, {
        filename: "/lib/python3.15/encodings/iso8859_16.py",
        start: 6862451,
        end: 6876008
      }, {
        filename: "/lib/python3.15/encodings/iso8859_2.py",
        start: 6876008,
        end: 6889412
      }, {
        filename: "/lib/python3.15/encodings/iso8859_3.py",
        start: 6889412,
        end: 6902501
      }, {
        filename: "/lib/python3.15/encodings/iso8859_4.py",
        start: 6902501,
        end: 6915877
      }, {
        filename: "/lib/python3.15/encodings/iso8859_5.py",
        start: 6915877,
        end: 6928892
      }, {
        filename: "/lib/python3.15/encodings/iso8859_6.py",
        start: 6928892,
        end: 6939725
      }, {
        filename: "/lib/python3.15/encodings/iso8859_7.py",
        start: 6939725,
        end: 6952569
      }, {
        filename: "/lib/python3.15/encodings/iso8859_8.py",
        start: 6952569,
        end: 6963605
      }, {
        filename: "/lib/python3.15/encodings/iso8859_9.py",
        start: 6963605,
        end: 6976761
      }, {
        filename: "/lib/python3.15/encodings/johab.py",
        start: 6976761,
        end: 6977784
      }, {
        filename: "/lib/python3.15/encodings/koi8_r.py",
        start: 6977784,
        end: 6991563
      }, {
        filename: "/lib/python3.15/encodings/koi8_t.py",
        start: 6991563,
        end: 7004756
      }, {
        filename: "/lib/python3.15/encodings/koi8_u.py",
        start: 7004756,
        end: 7018518
      }, {
        filename: "/lib/python3.15/encodings/kz1048.py",
        start: 7018518,
        end: 7032241
      }, {
        filename: "/lib/python3.15/encodings/latin_1.py",
        start: 7032241,
        end: 7033505
      }, {
        filename: "/lib/python3.15/encodings/mac_arabic.py",
        start: 7033505,
        end: 7069972
      }, {
        filename: "/lib/python3.15/encodings/mac_croatian.py",
        start: 7069972,
        end: 7083605
      }, {
        filename: "/lib/python3.15/encodings/mac_cyrillic.py",
        start: 7083605,
        end: 7097059
      }, {
        filename: "/lib/python3.15/encodings/mac_farsi.py",
        start: 7097059,
        end: 7112229
      }, {
        filename: "/lib/python3.15/encodings/mac_greek.py",
        start: 7112229,
        end: 7125950
      }, {
        filename: "/lib/python3.15/encodings/mac_iceland.py",
        start: 7125950,
        end: 7139448
      }, {
        filename: "/lib/python3.15/encodings/mac_latin2.py",
        start: 7139448,
        end: 7153566
      }, {
        filename: "/lib/python3.15/encodings/mac_roman.py",
        start: 7153566,
        end: 7167046
      }, {
        filename: "/lib/python3.15/encodings/mac_romanian.py",
        start: 7167046,
        end: 7180707
      }, {
        filename: "/lib/python3.15/encodings/mac_turkish.py",
        start: 7180707,
        end: 7194220
      }, {
        filename: "/lib/python3.15/encodings/mbcs.py",
        start: 7194220,
        end: 7195431
      }, {
        filename: "/lib/python3.15/encodings/oem.py",
        start: 7195431,
        end: 7196450
      }, {
        filename: "/lib/python3.15/encodings/palmos.py",
        start: 7196450,
        end: 7210002
      }, {
        filename: "/lib/python3.15/encodings/ptcp154.py",
        start: 7210002,
        end: 7224017
      }, {
        filename: "/lib/python3.15/encodings/punycode.py",
        start: 7224017,
        end: 7231660
      }, {
        filename: "/lib/python3.15/encodings/quopri_codec.py",
        start: 7231660,
        end: 7233185
      }, {
        filename: "/lib/python3.15/encodings/raw_unicode_escape.py",
        start: 7233185,
        end: 7234517
      }, {
        filename: "/lib/python3.15/encodings/rot_13.py",
        start: 7234517,
        end: 7236965
      }, {
        filename: "/lib/python3.15/encodings/shift_jis.py",
        start: 7236965,
        end: 7238004
      }, {
        filename: "/lib/python3.15/encodings/shift_jis_2004.py",
        start: 7238004,
        end: 7239063
      }, {
        filename: "/lib/python3.15/encodings/shift_jisx0213.py",
        start: 7239063,
        end: 7240122
      }, {
        filename: "/lib/python3.15/encodings/tis_620.py",
        start: 7240122,
        end: 7252422
      }, {
        filename: "/lib/python3.15/encodings/undefined.py",
        start: 7252422,
        end: 7253723
      }, {
        filename: "/lib/python3.15/encodings/unicode_escape.py",
        start: 7253723,
        end: 7255027
      }, {
        filename: "/lib/python3.15/encodings/utf_16.py",
        start: 7255027,
        end: 7260307
      }, {
        filename: "/lib/python3.15/encodings/utf_16_be.py",
        start: 7260307,
        end: 7261344
      }, {
        filename: "/lib/python3.15/encodings/utf_16_le.py",
        start: 7261344,
        end: 7262381
      }, {
        filename: "/lib/python3.15/encodings/utf_32.py",
        start: 7262381,
        end: 7267556
      }, {
        filename: "/lib/python3.15/encodings/utf_32_be.py",
        start: 7267556,
        end: 7268486
      }, {
        filename: "/lib/python3.15/encodings/utf_32_le.py",
        start: 7268486,
        end: 7269416
      }, {
        filename: "/lib/python3.15/encodings/utf_7.py",
        start: 7269416,
        end: 7270362
      }, {
        filename: "/lib/python3.15/encodings/utf_8.py",
        start: 7270362,
        end: 7271367
      }, {
        filename: "/lib/python3.15/encodings/utf_8_sig.py",
        start: 7271367,
        end: 7275500
      }, {
        filename: "/lib/python3.15/encodings/uu_codec.py",
        start: 7275500,
        end: 7278346
      }, {
        filename: "/lib/python3.15/encodings/zlib_codec.py",
        start: 7278346,
        end: 7280550
      }, {
        filename: "/lib/python3.15/ensurepip/__init__.py",
        start: 7280550,
        end: 7289003
      }, {
        filename: "/lib/python3.15/ensurepip/__main__.py",
        start: 7289003,
        end: 7289091
      }, {
        filename: "/lib/python3.15/ensurepip/_bundled/pip-25.3-py3-none-any.whl",
        start: 7289091,
        end: 9067713
      }, {
        filename: "/lib/python3.15/ensurepip/_uninstall.py",
        start: 9067713,
        end: 9068484
      }, {
        filename: "/lib/python3.15/enum.py",
        start: 9068484,
        end: 9155098
      }, {
        filename: "/lib/python3.15/filecmp.py",
        start: 9155098,
        end: 9165750
      }, {
        filename: "/lib/python3.15/fileinput.py",
        start: 9165750,
        end: 9181467
      }, {
        filename: "/lib/python3.15/fnmatch.py",
        start: 9181467,
        end: 9188258
      }, {
        filename: "/lib/python3.15/fractions.py",
        start: 9188258,
        end: 9229711
      }, {
        filename: "/lib/python3.15/ftplib.py",
        start: 9229711,
        end: 9264418
      }, {
        filename: "/lib/python3.15/functools.py",
        start: 9264418,
        end: 9308161
      }, {
        filename: "/lib/python3.15/genericpath.py",
        start: 9308161,
        end: 9314668
      }, {
        filename: "/lib/python3.15/getopt.py",
        start: 9314668,
        end: 9322759
      }, {
        filename: "/lib/python3.15/getpass.py",
        start: 9322759,
        end: 9331080
      }, {
        filename: "/lib/python3.15/gettext.py",
        start: 9331080,
        end: 9352675
      }, {
        filename: "/lib/python3.15/glob.py",
        start: 9352675,
        end: 9371741
      }, {
        filename: "/lib/python3.15/graphlib.py",
        start: 9371741,
        end: 9381514
      }, {
        filename: "/lib/python3.15/gzip.py",
        start: 9381514,
        end: 9406747
      }, {
        filename: "/lib/python3.15/hashlib.py",
        start: 9406747,
        end: 9418659
      }, {
        filename: "/lib/python3.15/heapq.py",
        start: 9418659,
        end: 9442091
      }, {
        filename: "/lib/python3.15/hmac.py",
        start: 9442091,
        end: 9452235
      }, {
        filename: "/lib/python3.15/html/__init__.py",
        start: 9452235,
        end: 9457010
      }, {
        filename: "/lib/python3.15/html/entities.py",
        start: 9457010,
        end: 9532522
      }, {
        filename: "/lib/python3.15/html/parser.py",
        start: 9532522,
        end: 9554256
      }, {
        filename: "/lib/python3.15/http/__init__.py",
        start: 9554256,
        end: 9563515
      }, {
        filename: "/lib/python3.15/http/client.py",
        start: 9563515,
        end: 9622048
      }, {
        filename: "/lib/python3.15/http/cookiejar.py",
        start: 9622048,
        end: 9699564
      }, {
        filename: "/lib/python3.15/http/cookies.py",
        start: 9699564,
        end: 9719593
      }, {
        filename: "/lib/python3.15/http/server.py",
        start: 9719593,
        end: 9759601
      }, {
        filename: "/lib/python3.15/idlelib/CREDITS.txt",
        start: 9759601,
        end: 9761770
      }, {
        filename: "/lib/python3.15/idlelib/ChangeLog",
        start: 9761770,
        end: 9818130
      }, {
        filename: "/lib/python3.15/idlelib/HISTORY.txt",
        start: 9818130,
        end: 9828455
      }, {
        filename: "/lib/python3.15/idlelib/Icons/README.txt",
        start: 9828455,
        end: 9830390
      }, {
        filename: "/lib/python3.15/idlelib/Icons/folder.gif",
        start: 9830390,
        end: 9830510
      }, {
        filename: "/lib/python3.15/idlelib/Icons/idle.ico",
        start: 9830510,
        end: 9888256
      }, {
        filename: "/lib/python3.15/idlelib/Icons/idle_16.gif",
        start: 9888256,
        end: 9888890
      }, {
        filename: "/lib/python3.15/idlelib/Icons/idle_16.png",
        start: 9888890,
        end: 9889921
      }, {
        filename: "/lib/python3.15/idlelib/Icons/idle_256.png",
        start: 9889921,
        end: 9921137
      }, {
        filename: "/lib/python3.15/idlelib/Icons/idle_32.gif",
        start: 9921137,
        end: 9922156
      }, {
        filename: "/lib/python3.15/idlelib/Icons/idle_32.png",
        start: 9922156,
        end: 9924192
      }, {
        filename: "/lib/python3.15/idlelib/Icons/idle_48.gif",
        start: 9924192,
        end: 9925580
      }, {
        filename: "/lib/python3.15/idlelib/Icons/idle_48.png",
        start: 9925580,
        end: 9929557
      }, {
        filename: "/lib/python3.15/idlelib/Icons/minusnode.gif",
        start: 9929557,
        end: 9929632
      }, {
        filename: "/lib/python3.15/idlelib/Icons/openfolder.gif",
        start: 9929632,
        end: 9929757
      }, {
        filename: "/lib/python3.15/idlelib/Icons/plusnode.gif",
        start: 9929757,
        end: 9929835
      }, {
        filename: "/lib/python3.15/idlelib/Icons/python.gif",
        start: 9929835,
        end: 9930215
      }, {
        filename: "/lib/python3.15/idlelib/Icons/tk.gif",
        start: 9930215,
        end: 9930287
      }, {
        filename: "/lib/python3.15/idlelib/NEWS2x.txt",
        start: 9930287,
        end: 9957459
      }, {
        filename: "/lib/python3.15/idlelib/News3.txt",
        start: 9957459,
        end: 10014274
      }, {
        filename: "/lib/python3.15/idlelib/README.txt",
        start: 10014274,
        end: 10025927
      }, {
        filename: "/lib/python3.15/idlelib/TODO.txt",
        start: 10025927,
        end: 10034404
      }, {
        filename: "/lib/python3.15/idlelib/__init__.py",
        start: 10034404,
        end: 10034800
      }, {
        filename: "/lib/python3.15/idlelib/__main__.py",
        start: 10034800,
        end: 10034907
      }, {
        filename: "/lib/python3.15/idlelib/autocomplete.py",
        start: 10034907,
        end: 10044261
      }, {
        filename: "/lib/python3.15/idlelib/autocomplete_w.py",
        start: 10044261,
        end: 10065124
      }, {
        filename: "/lib/python3.15/idlelib/autoexpand.py",
        start: 10065124,
        end: 10068340
      }, {
        filename: "/lib/python3.15/idlelib/browser.py",
        start: 10068340,
        end: 10076928
      }, {
        filename: "/lib/python3.15/idlelib/calltip.py",
        start: 10076928,
        end: 10084195
      }, {
        filename: "/lib/python3.15/idlelib/calltip_w.py",
        start: 10084195,
        end: 10091278
      }, {
        filename: "/lib/python3.15/idlelib/codecontext.py",
        start: 10091278,
        end: 10102698
      }, {
        filename: "/lib/python3.15/idlelib/colorizer.py",
        start: 10102698,
        end: 10117489
      }, {
        filename: "/lib/python3.15/idlelib/config-extensions.def",
        start: 10117489,
        end: 10119755
      }, {
        filename: "/lib/python3.15/idlelib/config-highlight.def",
        start: 10119755,
        end: 10122619
      }, {
        filename: "/lib/python3.15/idlelib/config-keys.def",
        start: 10122619,
        end: 10133529
      }, {
        filename: "/lib/python3.15/idlelib/config-main.def",
        start: 10133529,
        end: 10136640
      }, {
        filename: "/lib/python3.15/idlelib/config.py",
        start: 10136640,
        end: 10175043
      }, {
        filename: "/lib/python3.15/idlelib/config_key.py",
        start: 10175043,
        end: 10190273
      }, {
        filename: "/lib/python3.15/idlelib/configdialog.py",
        start: 10190273,
        end: 10295576
      }, {
        filename: "/lib/python3.15/idlelib/debugger.py",
        start: 10295576,
        end: 10316573
      }, {
        filename: "/lib/python3.15/idlelib/debugger_r.py",
        start: 10316573,
        end: 10328688
      }, {
        filename: "/lib/python3.15/idlelib/debugobj.py",
        start: 10328688,
        end: 10332865
      }, {
        filename: "/lib/python3.15/idlelib/debugobj_r.py",
        start: 10332865,
        end: 10333947
      }, {
        filename: "/lib/python3.15/idlelib/delegator.py",
        start: 10333947,
        end: 10334991
      }, {
        filename: "/lib/python3.15/idlelib/dynoption.py",
        start: 10334991,
        end: 10336984
      }, {
        filename: "/lib/python3.15/idlelib/editor.py",
        start: 10336984,
        end: 10404257
      }, {
        filename: "/lib/python3.15/idlelib/extend.txt",
        start: 10404257,
        end: 10407889
      }, {
        filename: "/lib/python3.15/idlelib/filelist.py",
        start: 10407889,
        end: 10411760
      }, {
        filename: "/lib/python3.15/idlelib/format.py",
        start: 10411760,
        end: 10427537
      }, {
        filename: "/lib/python3.15/idlelib/grep.py",
        start: 10427537,
        end: 10435058
      }, {
        filename: "/lib/python3.15/idlelib/help.html",
        start: 10435058,
        end: 10498661
      }, {
        filename: "/lib/python3.15/idlelib/help.py",
        start: 10498661,
        end: 10512347
      }, {
        filename: "/lib/python3.15/idlelib/help_about.py",
        start: 10512347,
        end: 10521370
      }, {
        filename: "/lib/python3.15/idlelib/history.py",
        start: 10521370,
        end: 10525435
      }, {
        filename: "/lib/python3.15/idlelib/hyperparser.py",
        start: 10525435,
        end: 10538324
      }, {
        filename: "/lib/python3.15/idlelib/idle.bat",
        start: 10538324,
        end: 10538501
      }, {
        filename: "/lib/python3.15/idlelib/idle.py",
        start: 10538501,
        end: 10538955
      }, {
        filename: "/lib/python3.15/idlelib/idle.pyw",
        start: 10538955,
        end: 10539525
      }, {
        filename: "/lib/python3.15/idlelib/idle_test/README.txt",
        start: 10539525,
        end: 10548405
      }, {
        filename: "/lib/python3.15/idlelib/idle_test/__init__.py",
        start: 10548405,
        end: 10549418
      }, {
        filename: "/lib/python3.15/idlelib/idle_test/example_noext",
        start: 10549418,
        end: 10549486
      }, {
        filename: "/lib/python3.15/idlelib/idle_test/example_stub.pyi",
        start: 10549486,
        end: 10549650
      }, {
        filename: "/lib/python3.15/idlelib/idle_test/htest.py",
        start: 10549650,
        end: 10564960
      }, {
        filename: "/lib/python3.15/idlelib/idle_test/mock_idle.py",
        start: 10564960,
        end: 10566903
      }, {
        filename: "/lib/python3.15/idlelib/idle_test/mock_tk.py",
        start: 10566903,
        end: 10578596
      }, {
        filename: "/lib/python3.15/idlelib/idle_test/template.py",
        start: 10578596,
        end: 10579238
      }, {
        filename: "/lib/python3.15/idlelib/idle_test/test_autocomplete.py",
        start: 10579238,
        end: 10590331
      }, {
        filename: "/lib/python3.15/idlelib/idle_test/test_autocomplete_w.py",
        start: 10590331,
        end: 10591051
      }, {
        filename: "/lib/python3.15/idlelib/idle_test/test_autoexpand.py",
        start: 10591051,
        end: 10595689
      }, {
        filename: "/lib/python3.15/idlelib/idle_test/test_browser.py",
        start: 10595689,
        end: 10604109
      }, {
        filename: "/lib/python3.15/idlelib/idle_test/test_calltip.py",
        start: 10604109,
        end: 10617767
      }, {
        filename: "/lib/python3.15/idlelib/idle_test/test_calltip_w.py",
        start: 10617767,
        end: 10618453
      }, {
        filename: "/lib/python3.15/idlelib/idle_test/test_codecontext.py",
        start: 10618453,
        end: 10634535
      }, {
        filename: "/lib/python3.15/idlelib/idle_test/test_colorizer.py",
        start: 10634535,
        end: 10657476
      }, {
        filename: "/lib/python3.15/idlelib/idle_test/test_config.py",
        start: 10657476,
        end: 10689567
      }, {
        filename: "/lib/python3.15/idlelib/idle_test/test_config_key.py",
        start: 10689567,
        end: 10701029
      }, {
        filename: "/lib/python3.15/idlelib/idle_test/test_configdialog.py",
        start: 10701029,
        end: 10756404
      }, {
        filename: "/lib/python3.15/idlelib/idle_test/test_debugger.py",
        start: 10756404,
        end: 10766125
      }, {
        filename: "/lib/python3.15/idlelib/idle_test/test_debugger_r.py",
        start: 10766125,
        end: 10767090
      }, {
        filename: "/lib/python3.15/idlelib/idle_test/test_debugobj.py",
        start: 10767090,
        end: 10768701
      }, {
        filename: "/lib/python3.15/idlelib/idle_test/test_debugobj_r.py",
        start: 10768701,
        end: 10769246
      }, {
        filename: "/lib/python3.15/idlelib/idle_test/test_delegator.py",
        start: 10769246,
        end: 10770813
      }, {
        filename: "/lib/python3.15/idlelib/idle_test/test_editmenu.py",
        start: 10770813,
        end: 10773377
      }, {
        filename: "/lib/python3.15/idlelib/idle_test/test_editor.py",
        start: 10773377,
        end: 10781528
      }, {
        filename: "/lib/python3.15/idlelib/idle_test/test_filelist.py",
        start: 10781528,
        end: 10782323
      }, {
        filename: "/lib/python3.15/idlelib/idle_test/test_format.py",
        start: 10782323,
        end: 10805933
      }, {
        filename: "/lib/python3.15/idlelib/idle_test/test_grep.py",
        start: 10805933,
        end: 10811e3
      }, {
        filename: "/lib/python3.15/idlelib/idle_test/test_help.py",
        start: 10811e3,
        end: 10811891
      }, {
        filename: "/lib/python3.15/idlelib/idle_test/test_help_about.py",
        start: 10811891,
        end: 10817795
      }, {
        filename: "/lib/python3.15/idlelib/idle_test/test_history.py",
        start: 10817795,
        end: 10823312
      }, {
        filename: "/lib/python3.15/idlelib/idle_test/test_hyperparser.py",
        start: 10823312,
        end: 10832394
      }, {
        filename: "/lib/python3.15/idlelib/idle_test/test_iomenu.py",
        start: 10832394,
        end: 10834851
      }, {
        filename: "/lib/python3.15/idlelib/idle_test/test_macosx.py",
        start: 10834851,
        end: 10838295
      }, {
        filename: "/lib/python3.15/idlelib/idle_test/test_mainmenu.py",
        start: 10838295,
        end: 10839933
      }, {
        filename: "/lib/python3.15/idlelib/idle_test/test_multicall.py",
        start: 10839933,
        end: 10841244
      }, {
        filename: "/lib/python3.15/idlelib/idle_test/test_outwin.py",
        start: 10841244,
        end: 10846967
      }, {
        filename: "/lib/python3.15/idlelib/idle_test/test_parenmatch.py",
        start: 10846967,
        end: 10850511
      }, {
        filename: "/lib/python3.15/idlelib/idle_test/test_pathbrowser.py",
        start: 10850511,
        end: 10852933
      }, {
        filename: "/lib/python3.15/idlelib/idle_test/test_percolator.py",
        start: 10852933,
        end: 10856998
      }, {
        filename: "/lib/python3.15/idlelib/idle_test/test_pyparse.py",
        start: 10856998,
        end: 10876363
      }, {
        filename: "/lib/python3.15/idlelib/idle_test/test_pyshell.py",
        start: 10876363,
        end: 10881328
      }, {
        filename: "/lib/python3.15/idlelib/idle_test/test_query.py",
        start: 10881328,
        end: 10896767
      }, {
        filename: "/lib/python3.15/idlelib/idle_test/test_redirector.py",
        start: 10896767,
        end: 10900939
      }, {
        filename: "/lib/python3.15/idlelib/idle_test/test_replace.py",
        start: 10900939,
        end: 10909238
      }, {
        filename: "/lib/python3.15/idlelib/idle_test/test_rpc.py",
        start: 10909238,
        end: 10910043
      }, {
        filename: "/lib/python3.15/idlelib/idle_test/test_run.py",
        start: 10910043,
        end: 10925894
      }, {
        filename: "/lib/python3.15/idlelib/idle_test/test_runscript.py",
        start: 10925894,
        end: 10926671
      }, {
        filename: "/lib/python3.15/idlelib/idle_test/test_scrolledlist.py",
        start: 10926671,
        end: 10927167
      }, {
        filename: "/lib/python3.15/idlelib/idle_test/test_search.py",
        start: 10927167,
        end: 10929626
      }, {
        filename: "/lib/python3.15/idlelib/idle_test/test_searchbase.py",
        start: 10929626,
        end: 10935317
      }, {
        filename: "/lib/python3.15/idlelib/idle_test/test_searchengine.py",
        start: 10935317,
        end: 10946905
      }, {
        filename: "/lib/python3.15/idlelib/idle_test/test_sidebar.py",
        start: 10946905,
        end: 10973749
      }, {
        filename: "/lib/python3.15/idlelib/idle_test/test_squeezer.py",
        start: 10973749,
        end: 10993405
      }, {
        filename: "/lib/python3.15/idlelib/idle_test/test_stackviewer.py",
        start: 10993405,
        end: 10994396
      }, {
        filename: "/lib/python3.15/idlelib/idle_test/test_statusbar.py",
        start: 10994396,
        end: 10995529
      }, {
        filename: "/lib/python3.15/idlelib/idle_test/test_text.py",
        start: 10995529,
        end: 11002499
      }, {
        filename: "/lib/python3.15/idlelib/idle_test/test_textview.py",
        start: 11002499,
        end: 11009863
      }, {
        filename: "/lib/python3.15/idlelib/idle_test/test_tooltip.py",
        start: 11009863,
        end: 11015248
      }, {
        filename: "/lib/python3.15/idlelib/idle_test/test_tree.py",
        start: 11015248,
        end: 11017e3
      }, {
        filename: "/lib/python3.15/idlelib/idle_test/test_undo.py",
        start: 11017e3,
        end: 11021228
      }, {
        filename: "/lib/python3.15/idlelib/idle_test/test_util.py",
        start: 11021228,
        end: 11021536
      }, {
        filename: "/lib/python3.15/idlelib/idle_test/test_warning.py",
        start: 11021536,
        end: 11024276
      }, {
        filename: "/lib/python3.15/idlelib/idle_test/test_window.py",
        start: 11024276,
        end: 11025351
      }, {
        filename: "/lib/python3.15/idlelib/idle_test/test_zoomheight.py",
        start: 11025351,
        end: 11026350
      }, {
        filename: "/lib/python3.15/idlelib/idle_test/test_zzdummy.py",
        start: 11026350,
        end: 11030805
      }, {
        filename: "/lib/python3.15/idlelib/idle_test/tkinter_testing_utils.py",
        start: 11030805,
        end: 11033138
      }, {
        filename: "/lib/python3.15/idlelib/iomenu.py",
        start: 11033138,
        end: 11049297
      }, {
        filename: "/lib/python3.15/idlelib/macosx.py",
        start: 11049297,
        end: 11058587
      }, {
        filename: "/lib/python3.15/idlelib/mainmenu.py",
        start: 11058587,
        end: 11062525
      }, {
        filename: "/lib/python3.15/idlelib/multicall.py",
        start: 11062525,
        end: 11081177
      }, {
        filename: "/lib/python3.15/idlelib/outwin.py",
        start: 11081177,
        end: 11086882
      }, {
        filename: "/lib/python3.15/idlelib/parenmatch.py",
        start: 11086882,
        end: 11094086
      }, {
        filename: "/lib/python3.15/idlelib/pathbrowser.py",
        start: 11094086,
        end: 11097179
      }, {
        filename: "/lib/python3.15/idlelib/percolator.py",
        start: 11097179,
        end: 11100747
      }, {
        filename: "/lib/python3.15/idlelib/pyparse.py",
        start: 11100747,
        end: 11120611
      }, {
        filename: "/lib/python3.15/idlelib/pyshell.py",
        start: 11120611,
        end: 11182997
      }, {
        filename: "/lib/python3.15/idlelib/query.py",
        start: 11182997,
        end: 11197975
      }, {
        filename: "/lib/python3.15/idlelib/redirector.py",
        start: 11197975,
        end: 11204807
      }, {
        filename: "/lib/python3.15/idlelib/replace.py",
        start: 11204807,
        end: 11214605
      }, {
        filename: "/lib/python3.15/idlelib/rpc.py",
        start: 11214605,
        end: 11235683
      }, {
        filename: "/lib/python3.15/idlelib/run.py",
        start: 11235683,
        end: 11257560
      }, {
        filename: "/lib/python3.15/idlelib/runscript.py",
        start: 11257560,
        end: 11265833
      }, {
        filename: "/lib/python3.15/idlelib/scrolledlist.py",
        start: 11265833,
        end: 11270311
      }, {
        filename: "/lib/python3.15/idlelib/search.py",
        start: 11270311,
        end: 11275878
      }, {
        filename: "/lib/python3.15/idlelib/searchbase.py",
        start: 11275878,
        end: 11283730
      }, {
        filename: "/lib/python3.15/idlelib/searchengine.py",
        start: 11283730,
        end: 11291102
      }, {
        filename: "/lib/python3.15/idlelib/sidebar.py",
        start: 11291102,
        end: 11311429
      }, {
        filename: "/lib/python3.15/idlelib/squeezer.py",
        start: 11311429,
        end: 11324263
      }, {
        filename: "/lib/python3.15/idlelib/stackviewer.py",
        start: 11324263,
        end: 11328279
      }, {
        filename: "/lib/python3.15/idlelib/statusbar.py",
        start: 11328279,
        end: 11329753
      }, {
        filename: "/lib/python3.15/idlelib/textview.py",
        start: 11329753,
        end: 11336537
      }, {
        filename: "/lib/python3.15/idlelib/tooltip.py",
        start: 11336537,
        end: 11343202
      }, {
        filename: "/lib/python3.15/idlelib/tree.py",
        start: 11343202,
        end: 11359975
      }, {
        filename: "/lib/python3.15/idlelib/undo.py",
        start: 11359975,
        end: 11370991
      }, {
        filename: "/lib/python3.15/idlelib/util.py",
        start: 11370991,
        end: 11372303
      }, {
        filename: "/lib/python3.15/idlelib/window.py",
        start: 11372303,
        end: 11374919
      }, {
        filename: "/lib/python3.15/idlelib/zoomheight.py",
        start: 11374919,
        end: 11379122
      }, {
        filename: "/lib/python3.15/idlelib/zzdummy.py",
        start: 11379122,
        end: 11381127
      }, {
        filename: "/lib/python3.15/imaplib.py",
        start: 11381127,
        end: 11447870
      }, {
        filename: "/lib/python3.15/importlib/__init__.py",
        start: 11447870,
        end: 11452929
      }, {
        filename: "/lib/python3.15/importlib/__pycache__/__init__.cpython-315.pyc",
        start: 11452929,
        end: 11457912
      }, {
        filename: "/lib/python3.15/importlib/__pycache__/_abc.cpython-315.pyc",
        start: 11457912,
        end: 11458915
      }, {
        filename: "/lib/python3.15/importlib/_abc.py",
        start: 11458915,
        end: 11459629
      }, {
        filename: "/lib/python3.15/importlib/_bootstrap.py",
        start: 11459629,
        end: 11513455
      }, {
        filename: "/lib/python3.15/importlib/_bootstrap_external.py",
        start: 11513455,
        end: 11570013
      }, {
        filename: "/lib/python3.15/importlib/abc.py",
        start: 11570013,
        end: 11577561
      }, {
        filename: "/lib/python3.15/importlib/machinery.py",
        start: 11577561,
        end: 11579774
      }, {
        filename: "/lib/python3.15/importlib/metadata/__init__.py",
        start: 11579774,
        end: 11616495
      }, {
        filename: "/lib/python3.15/importlib/metadata/_adapters.py",
        start: 11616495,
        end: 11620279
      }, {
        filename: "/lib/python3.15/importlib/metadata/_collections.py",
        start: 11620279,
        end: 11621039
      }, {
        filename: "/lib/python3.15/importlib/metadata/_functools.py",
        start: 11621039,
        end: 11623934
      }, {
        filename: "/lib/python3.15/importlib/metadata/_itertools.py",
        start: 11623934,
        end: 11629285
      }, {
        filename: "/lib/python3.15/importlib/metadata/_meta.py",
        start: 11629285,
        end: 11631050
      }, {
        filename: "/lib/python3.15/importlib/metadata/_text.py",
        start: 11631050,
        end: 11633216
      }, {
        filename: "/lib/python3.15/importlib/metadata/_typing.py",
        start: 11633216,
        end: 11633583
      }, {
        filename: "/lib/python3.15/importlib/metadata/diagnose.py",
        start: 11633583,
        end: 11633962
      }, {
        filename: "/lib/python3.15/importlib/readers.py",
        start: 11633962,
        end: 11634289
      }, {
        filename: "/lib/python3.15/importlib/resources/__init__.py",
        start: 11634289,
        end: 11634992
      }, {
        filename: "/lib/python3.15/importlib/resources/_adapters.py",
        start: 11634992,
        end: 11639474
      }, {
        filename: "/lib/python3.15/importlib/resources/_common.py",
        start: 11639474,
        end: 11644166
      }, {
        filename: "/lib/python3.15/importlib/resources/_functional.py",
        start: 11644166,
        end: 11646817
      }, {
        filename: "/lib/python3.15/importlib/resources/_itertools.py",
        start: 11646817,
        end: 11648094
      }, {
        filename: "/lib/python3.15/importlib/resources/abc.py",
        start: 11648094,
        end: 11653297
      }, {
        filename: "/lib/python3.15/importlib/resources/readers.py",
        start: 11653297,
        end: 11659540
      }, {
        filename: "/lib/python3.15/importlib/resources/simple.py",
        start: 11659540,
        end: 11662130
      }, {
        filename: "/lib/python3.15/importlib/simple.py",
        start: 11662130,
        end: 11662484
      }, {
        filename: "/lib/python3.15/importlib/util.py",
        start: 11662484,
        end: 11673898
      }, {
        filename: "/lib/python3.15/inspect.py",
        start: 11673898,
        end: 11801986
      }, {
        filename: "/lib/python3.15/io.py",
        start: 11801986,
        end: 11806722
      }, {
        filename: "/lib/python3.15/ipaddress.py",
        start: 11806722,
        end: 11888229
      }, {
        filename: "/lib/python3.15/json/__init__.py",
        start: 11888229,
        end: 11902536
      }, {
        filename: "/lib/python3.15/json/__main__.py",
        start: 11902536,
        end: 11902957
      }, {
        filename: "/lib/python3.15/json/__pycache__/__init__.cpython-315.pyc",
        start: 11902957,
        end: 11917449
      }, {
        filename: "/lib/python3.15/json/__pycache__/decoder.cpython-315.pyc",
        start: 11917449,
        end: 11931986
      }, {
        filename: "/lib/python3.15/json/__pycache__/encoder.cpython-315.pyc",
        start: 11931986,
        end: 11949694
      }, {
        filename: "/lib/python3.15/json/__pycache__/scanner.cpython-315.pyc",
        start: 11949694,
        end: 11953246
      }, {
        filename: "/lib/python3.15/json/decoder.py",
        start: 11953246,
        end: 11966119
      }, {
        filename: "/lib/python3.15/json/encoder.py",
        start: 11966119,
        end: 11983193
      }, {
        filename: "/lib/python3.15/json/scanner.py",
        start: 11983193,
        end: 11985627
      }, {
        filename: "/lib/python3.15/json/tool.py",
        start: 11985627,
        end: 11990254
      }, {
        filename: "/lib/python3.15/keyword.py",
        start: 11990254,
        end: 11991327
      }, {
        filename: "/lib/python3.15/linecache.py",
        start: 11991327,
        end: 12000480
      }, {
        filename: "/lib/python3.15/locale.py",
        start: 12000480,
        end: 12080115
      }, {
        filename: "/lib/python3.15/logging/__init__.py",
        start: 12080115,
        end: 12165141
      }, {
        filename: "/lib/python3.15/logging/__pycache__/__init__.cpython-315.pyc",
        start: 12165141,
        end: 12263419
      }, {
        filename: "/lib/python3.15/logging/config.py",
        start: 12263419,
        end: 12306403
      }, {
        filename: "/lib/python3.15/logging/handlers.py",
        start: 12306403,
        end: 12369195
      }, {
        filename: "/lib/python3.15/lzma.py",
        start: 12369195,
        end: 12382621
      }, {
        filename: "/lib/python3.15/mailbox.py",
        start: 12382621,
        end: 12464214
      }, {
        filename: "/lib/python3.15/mimetypes.py",
        start: 12464214,
        end: 12490961
      }, {
        filename: "/lib/python3.15/modulefinder.py",
        start: 12490961,
        end: 12515200
      }, {
        filename: "/lib/python3.15/multiprocessing/__init__.py",
        start: 12515200,
        end: 12516116
      }, {
        filename: "/lib/python3.15/multiprocessing/connection.py",
        start: 12516116,
        end: 12558674
      }, {
        filename: "/lib/python3.15/multiprocessing/context.py",
        start: 12558674,
        end: 12570449
      }, {
        filename: "/lib/python3.15/multiprocessing/dummy/__init__.py",
        start: 12570449,
        end: 12573512
      }, {
        filename: "/lib/python3.15/multiprocessing/dummy/connection.py",
        start: 12573512,
        end: 12575110
      }, {
        filename: "/lib/python3.15/multiprocessing/forkserver.py",
        start: 12575110,
        end: 12590475
      }, {
        filename: "/lib/python3.15/multiprocessing/heap.py",
        start: 12590475,
        end: 12601910
      }, {
        filename: "/lib/python3.15/multiprocessing/managers.py",
        start: 12601910,
        end: 12651656
      }, {
        filename: "/lib/python3.15/multiprocessing/pool.py",
        start: 12651656,
        end: 12684424
      }, {
        filename: "/lib/python3.15/multiprocessing/popen_fork.py",
        start: 12684424,
        end: 12687007
      }, {
        filename: "/lib/python3.15/multiprocessing/popen_forkserver.py",
        start: 12687007,
        end: 12689237
      }, {
        filename: "/lib/python3.15/multiprocessing/popen_spawn_posix.py",
        start: 12689237,
        end: 12691380
      }, {
        filename: "/lib/python3.15/multiprocessing/popen_spawn_win32.py",
        start: 12691380,
        end: 12696015
      }, {
        filename: "/lib/python3.15/multiprocessing/process.py",
        start: 12696015,
        end: 12708248
      }, {
        filename: "/lib/python3.15/multiprocessing/queues.py",
        start: 12708248,
        end: 12720906
      }, {
        filename: "/lib/python3.15/multiprocessing/reduction.py",
        start: 12720906,
        end: 12730536
      }, {
        filename: "/lib/python3.15/multiprocessing/resource_sharer.py",
        start: 12730536,
        end: 12735681
      }, {
        filename: "/lib/python3.15/multiprocessing/resource_tracker.py",
        start: 12735681,
        end: 12750875
      }, {
        filename: "/lib/python3.15/multiprocessing/shared_memory.py",
        start: 12750875,
        end: 12769791
      }, {
        filename: "/lib/python3.15/multiprocessing/sharedctypes.py",
        start: 12769791,
        end: 12776289
      }, {
        filename: "/lib/python3.15/multiprocessing/spawn.py",
        start: 12776289,
        end: 12785933
      }, {
        filename: "/lib/python3.15/multiprocessing/synchronize.py",
        start: 12785933,
        end: 12798232
      }, {
        filename: "/lib/python3.15/multiprocessing/util.py",
        start: 12798232,
        end: 12815660
      }, {
        filename: "/lib/python3.15/netrc.py",
        start: 12815660,
        end: 12822679
      }, {
        filename: "/lib/python3.15/ntpath.py",
        start: 12822679,
        end: 12853905
      }, {
        filename: "/lib/python3.15/nturl2path.py",
        start: 12853905,
        end: 12856348
      }, {
        filename: "/lib/python3.15/numbers.py",
        start: 12856348,
        end: 12868117
      }, {
        filename: "/lib/python3.15/opcode.py",
        start: 12868117,
        end: 12871269
      }, {
        filename: "/lib/python3.15/operator.py",
        start: 12871269,
        end: 12882427
      }, {
        filename: "/lib/python3.15/optparse.py",
        start: 12882427,
        end: 12942865
      }, {
        filename: "/lib/python3.15/os.py",
        start: 12942865,
        end: 12985317
      }, {
        filename: "/lib/python3.15/pathlib/__init__.py",
        start: 12985317,
        end: 13039557
      }, {
        filename: "/lib/python3.15/pathlib/__pycache__/__init__.cpython-315.pyc",
        start: 13039557,
        end: 13110461
      }, {
        filename: "/lib/python3.15/pathlib/__pycache__/_os.cpython-315.pyc",
        start: 13110461,
        end: 13121609
      }, {
        filename: "/lib/python3.15/pathlib/_local.py",
        start: 13121609,
        end: 13121871
      }, {
        filename: "/lib/python3.15/pathlib/_os.py",
        start: 13121871,
        end: 13131388
      }, {
        filename: "/lib/python3.15/pathlib/types.py",
        start: 13131388,
        end: 13147870
      }, {
        filename: "/lib/python3.15/pdb.py",
        start: 13147870,
        end: 13283043
      }, {
        filename: "/lib/python3.15/pickle.py",
        start: 13283043,
        end: 13353711
      }, {
        filename: "/lib/python3.15/pickletools.py",
        start: 13353711,
        end: 13447116
      }, {
        filename: "/lib/python3.15/pkgutil.py",
        start: 13447116,
        end: 13463171
      }, {
        filename: "/lib/python3.15/platform.py",
        start: 13463171,
        end: 13509861
      }, {
        filename: "/lib/python3.15/plistlib.py",
        start: 13509861,
        end: 13539895
      }, {
        filename: "/lib/python3.15/poplib.py",
        start: 13539895,
        end: 13554499
      }, {
        filename: "/lib/python3.15/posixpath.py",
        start: 13554499,
        end: 13573574
      }, {
        filename: "/lib/python3.15/pprint.py",
        start: 13573574,
        end: 13601382
      }, {
        filename: "/lib/python3.15/profile.py",
        start: 13601382,
        end: 13624729
      }, {
        filename: "/lib/python3.15/profiling/__init__.py",
        start: 13624729,
        end: 13625150
      }, {
        filename: "/lib/python3.15/profiling/sampling/__init__.py",
        start: 13625150,
        end: 13625712
      }, {
        filename: "/lib/python3.15/profiling/sampling/__main__.py",
        start: 13625712,
        end: 13628628
      }, {
        filename: "/lib/python3.15/profiling/sampling/_assets/python-logo-only.png",
        start: 13628628,
        end: 13641348
      }, {
        filename: "/lib/python3.15/profiling/sampling/_assets/tachyon-logo.png",
        start: 13641348,
        end: 13790963
      }, {
        filename: "/lib/python3.15/profiling/sampling/_child_monitor.py",
        start: 13790963,
        end: 13800012
      }, {
        filename: "/lib/python3.15/profiling/sampling/_css_utils.py",
        start: 13800012,
        end: 13800733
      }, {
        filename: "/lib/python3.15/profiling/sampling/_flamegraph_assets/flamegraph.css",
        start: 13800733,
        end: 13822604
      }, {
        filename: "/lib/python3.15/profiling/sampling/_flamegraph_assets/flamegraph.js",
        start: 13822604,
        end: 13866747
      }, {
        filename: "/lib/python3.15/profiling/sampling/_flamegraph_assets/flamegraph_template.html",
        start: 13866747,
        end: 13885813
      }, {
        filename: "/lib/python3.15/profiling/sampling/_heatmap_assets/heatmap.css",
        start: 13885813,
        end: 13917336
      }, {
        filename: "/lib/python3.15/profiling/sampling/_heatmap_assets/heatmap.js",
        start: 13917336,
        end: 13942998
      }, {
        filename: "/lib/python3.15/profiling/sampling/_heatmap_assets/heatmap_index.js",
        start: 13942998,
        end: 13946655
      }, {
        filename: "/lib/python3.15/profiling/sampling/_heatmap_assets/heatmap_index_template.html",
        start: 13946655,
        end: 13954052
      }, {
        filename: "/lib/python3.15/profiling/sampling/_heatmap_assets/heatmap_pyfile_template.html",
        start: 13954052,
        end: 13962215
      }, {
        filename: "/lib/python3.15/profiling/sampling/_heatmap_assets/heatmap_shared.js",
        start: 13962215,
        end: 13965638
      }, {
        filename: "/lib/python3.15/profiling/sampling/_shared_assets/base.css",
        start: 13965638,
        end: 13977009
      }, {
        filename: "/lib/python3.15/profiling/sampling/_sync_coordinator.py",
        start: 13977009,
        end: 13984814
      }, {
        filename: "/lib/python3.15/profiling/sampling/_vendor/d3-flame-graph/4.1.3/d3-flamegraph-tooltip.min.js",
        start: 13984814,
        end: 14022535
      }, {
        filename: "/lib/python3.15/profiling/sampling/_vendor/d3-flame-graph/4.1.3/d3-flamegraph.css",
        start: 14022535,
        end: 14023320
      }, {
        filename: "/lib/python3.15/profiling/sampling/_vendor/d3-flame-graph/4.1.3/d3-flamegraph.min.js",
        start: 14023320,
        end: 14081914
      }, {
        filename: "/lib/python3.15/profiling/sampling/_vendor/d3/7.8.5/d3.min.js",
        start: 14081914,
        end: 14361547
      }, {
        filename: "/lib/python3.15/profiling/sampling/cli.py",
        start: 14361547,
        end: 14392236
      }, {
        filename: "/lib/python3.15/profiling/sampling/collector.py",
        start: 14392236,
        end: 14402067
      }, {
        filename: "/lib/python3.15/profiling/sampling/constants.py",
        start: 14402067,
        end: 14403194
      }, {
        filename: "/lib/python3.15/profiling/sampling/errors.py",
        start: 14403194,
        end: 14403918
      }, {
        filename: "/lib/python3.15/profiling/sampling/gecko_collector.py",
        start: 14403918,
        end: 14435614
      }, {
        filename: "/lib/python3.15/profiling/sampling/heatmap_collector.py",
        start: 14435614,
        end: 14485690
      }, {
        filename: "/lib/python3.15/profiling/sampling/live_collector/__init__.py",
        start: 14485690,
        end: 14495374
      }, {
        filename: "/lib/python3.15/profiling/sampling/live_collector/collector.py",
        start: 14495374,
        end: 14538881
      }, {
        filename: "/lib/python3.15/profiling/sampling/live_collector/constants.py",
        start: 14538881,
        end: 14540371
      }, {
        filename: "/lib/python3.15/profiling/sampling/live_collector/display.py",
        start: 14540371,
        end: 14546783
      }, {
        filename: "/lib/python3.15/profiling/sampling/live_collector/trend_tracker.py",
        start: 14546783,
        end: 14551777
      }, {
        filename: "/lib/python3.15/profiling/sampling/live_collector/widgets.py",
        start: 14551777,
        end: 14590277
      }, {
        filename: "/lib/python3.15/profiling/sampling/opcode_utils.py",
        start: 14590277,
        end: 14593598
      }, {
        filename: "/lib/python3.15/profiling/sampling/pstats_collector.py",
        start: 14593598,
        end: 14611035
      }, {
        filename: "/lib/python3.15/profiling/sampling/sample.py",
        start: 14611035,
        end: 14628352
      }, {
        filename: "/lib/python3.15/profiling/sampling/stack_collector.py",
        start: 14628352,
        end: 14645174
      }, {
        filename: "/lib/python3.15/profiling/sampling/string_table.py",
        start: 14645174,
        end: 14646615
      }, {
        filename: "/lib/python3.15/profiling/tracing/__init__.py",
        start: 14646615,
        end: 14654403
      }, {
        filename: "/lib/python3.15/profiling/tracing/__main__.py",
        start: 14654403,
        end: 14654532
      }, {
        filename: "/lib/python3.15/profiling/tracing/_utils.py",
        start: 14654532,
        end: 14655425
      }, {
        filename: "/lib/python3.15/pstats.py",
        start: 14655425,
        end: 14687422
      }, {
        filename: "/lib/python3.15/pty.py",
        start: 14687422,
        end: 14692634
      }, {
        filename: "/lib/python3.15/py_compile.py",
        start: 14692634,
        end: 14700483
      }, {
        filename: "/lib/python3.15/pyclbr.py",
        start: 14700483,
        end: 14711866
      }, {
        filename: "/lib/python3.15/pydoc.py",
        start: 14711866,
        end: 14821108
      }, {
        filename: "/lib/python3.15/pydoc_data/__init__.py",
        start: 14821108,
        end: 14821108
      }, {
        filename: "/lib/python3.15/pydoc_data/_pydoc.css",
        start: 14821108,
        end: 14822433
      }, {
        filename: "/lib/python3.15/pydoc_data/topics.py",
        start: 14822433,
        end: 15402301
      }, {
        filename: "/lib/python3.15/queue.py",
        start: 15402301,
        end: 15415756
      }, {
        filename: "/lib/python3.15/quopri.py",
        start: 15415756,
        end: 15422915
      }, {
        filename: "/lib/python3.15/random.py",
        start: 15422915,
        end: 15460175
      }, {
        filename: "/lib/python3.15/re/__init__.py",
        start: 15460175,
        end: 15478453
      }, {
        filename: "/lib/python3.15/re/__pycache__/__init__.cpython-315.pyc",
        start: 15478453,
        end: 15498970
      }, {
        filename: "/lib/python3.15/re/__pycache__/_casefix.cpython-315.pyc",
        start: 15498970,
        end: 15500776
      }, {
        filename: "/lib/python3.15/re/__pycache__/_compiler.cpython-315.pyc",
        start: 15500776,
        end: 15530550
      }, {
        filename: "/lib/python3.15/re/__pycache__/_constants.cpython-315.pyc",
        start: 15530550,
        end: 15536171
      }, {
        filename: "/lib/python3.15/re/__pycache__/_parser.cpython-315.pyc",
        start: 15536171,
        end: 15581604
      }, {
        filename: "/lib/python3.15/re/_casefix.py",
        start: 15581604,
        end: 15587048
      }, {
        filename: "/lib/python3.15/re/_compiler.py",
        start: 15587048,
        end: 15613909
      }, {
        filename: "/lib/python3.15/re/_constants.py",
        start: 15613909,
        end: 15619945
      }, {
        filename: "/lib/python3.15/re/_parser.py",
        start: 15619945,
        end: 15660272
      }, {
        filename: "/lib/python3.15/reprlib.py",
        start: 15660272,
        end: 15668336
      }, {
        filename: "/lib/python3.15/rlcompleter.py",
        start: 15668336,
        end: 15676254
      }, {
        filename: "/lib/python3.15/runpy.py",
        start: 15676254,
        end: 15689106
      }, {
        filename: "/lib/python3.15/sched.py",
        start: 15689106,
        end: 15695457
      }, {
        filename: "/lib/python3.15/secrets.py",
        start: 15695457,
        end: 15697441
      }, {
        filename: "/lib/python3.15/selectors.py",
        start: 15697441,
        end: 15716898
      }, {
        filename: "/lib/python3.15/shelve.py",
        start: 15716898,
        end: 15726546
      }, {
        filename: "/lib/python3.15/shlex.py",
        start: 15726546,
        end: 15740302
      }, {
        filename: "/lib/python3.15/shutil.py",
        start: 15740302,
        end: 15800870
      }, {
        filename: "/lib/python3.15/signal.py",
        start: 15800870,
        end: 15803365
      }, {
        filename: "/lib/python3.15/site-packages/README.txt",
        start: 15803365,
        end: 15803484
      }, {
        filename: "/lib/python3.15/site.py",
        start: 15803484,
        end: 15829077
      }, {
        filename: "/lib/python3.15/smtplib.py",
        start: 15829077,
        end: 15872970
      }, {
        filename: "/lib/python3.15/socket.py",
        start: 15872970,
        end: 15910297
      }, {
        filename: "/lib/python3.15/socketserver.py",
        start: 15910297,
        end: 15938631
      }, {
        filename: "/lib/python3.15/sqlite3/__init__.py",
        start: 15938631,
        end: 15940645
      }, {
        filename: "/lib/python3.15/sqlite3/__main__.py",
        start: 15940645,
        end: 15945750
      }, {
        filename: "/lib/python3.15/sqlite3/_completer.py",
        start: 15945750,
        end: 15949543
      }, {
        filename: "/lib/python3.15/sqlite3/dbapi2.py",
        start: 15949543,
        end: 15952663
      }, {
        filename: "/lib/python3.15/sqlite3/dump.py",
        start: 15952663,
        end: 15956903
      }, {
        filename: "/lib/python3.15/ssl.py",
        start: 15956903,
        end: 16011110
      }, {
        filename: "/lib/python3.15/stat.py",
        start: 16011110,
        end: 16017702
      }, {
        filename: "/lib/python3.15/statistics.py",
        start: 16017702,
        end: 16079948
      }, {
        filename: "/lib/python3.15/string/__init__.py",
        start: 16079948,
        end: 16092155
      }, {
        filename: "/lib/python3.15/string/__pycache__/__init__.cpython-315.pyc",
        start: 16092155,
        end: 16105553
      }, {
        filename: "/lib/python3.15/string/templatelib.py",
        start: 16105553,
        end: 16106509
      }, {
        filename: "/lib/python3.15/stringprep.py",
        start: 16106509,
        end: 16119426
      }, {
        filename: "/lib/python3.15/struct.py",
        start: 16119426,
        end: 16119711
      }, {
        filename: "/lib/python3.15/subprocess.py",
        start: 16119711,
        end: 16210471
      }, {
        filename: "/lib/python3.15/symtable.py",
        start: 16210471,
        end: 16224928
      }, {
        filename: "/lib/python3.15/sysconfig/__init__.py",
        start: 16224928,
        end: 16253496
      }, {
        filename: "/lib/python3.15/sysconfig/__main__.py",
        start: 16253496,
        end: 16261573
      }, {
        filename: "/lib/python3.15/sysconfig/__pycache__/__init__.cpython-315.pyc",
        start: 16261573,
        end: 16290241
      }, {
        filename: "/lib/python3.15/sysconfig/__pycache__/__main__.cpython-315.pyc",
        start: 16290241,
        end: 16299999
      }, {
        filename: "/lib/python3.15/tabnanny.py",
        start: 16299999,
        end: 16311746
      }, {
        filename: "/lib/python3.15/tarfile.py",
        start: 16311746,
        end: 16429310
      }, {
        filename: "/lib/python3.15/tempfile.py",
        start: 16429310,
        end: 16462194
      }, {
        filename: "/lib/python3.15/test/.ruff.toml",
        start: 16462194,
        end: 16463393
      }, {
        filename: "/lib/python3.15/test/NormalizationTest-3.2.0.txt",
        start: 16463393,
        end: 18489368
      }, {
        filename: "/lib/python3.15/test/__init__.py",
        start: 18489368,
        end: 18489415
      }, {
        filename: "/lib/python3.15/test/__main__.py",
        start: 18489415,
        end: 18489482
      }, {
        filename: "/lib/python3.15/test/_code_definitions.py",
        start: 18489482,
        end: 18495743
      }, {
        filename: "/lib/python3.15/test/_crossinterp_definitions.py",
        start: 18495743,
        end: 18497777
      }, {
        filename: "/lib/python3.15/test/_test_atexit.py",
        start: 18497777,
        end: 18502194
      }, {
        filename: "/lib/python3.15/test/_test_eintr.py",
        start: 18502194,
        end: 18520827
      }, {
        filename: "/lib/python3.15/test/_test_embed_structseq.py",
        start: 18520827,
        end: 18522888
      }, {
        filename: "/lib/python3.15/test/_test_gc_fast_cycles.py",
        start: 18522888,
        end: 18524377
      }, {
        filename: "/lib/python3.15/test/_test_monitoring_shutdown.py",
        start: 18524377,
        end: 18525104
      }, {
        filename: "/lib/python3.15/test/_test_multiprocessing.py",
        start: 18525104,
        end: 18783051
      }, {
        filename: "/lib/python3.15/test/_test_venv_multiprocessing.py",
        start: 18783051,
        end: 18783847
      }, {
        filename: "/lib/python3.15/test/archiver_tests.py",
        start: 18783847,
        end: 18791074
      }, {
        filename: "/lib/python3.15/test/archivetestdata/README.md",
        start: 18791074,
        end: 18792184
      }, {
        filename: "/lib/python3.15/test/archivetestdata/exe_with_z64",
        start: 18792184,
        end: 18793162
      }, {
        filename: "/lib/python3.15/test/archivetestdata/exe_with_zip",
        start: 18793162,
        end: 18794152
      }, {
        filename: "/lib/python3.15/test/archivetestdata/header.sh",
        start: 18794152,
        end: 18794865
      }, {
        filename: "/lib/python3.15/test/archivetestdata/recursion.tar",
        start: 18794865,
        end: 18795381
      }, {
        filename: "/lib/python3.15/test/archivetestdata/testdata_module_inside_zip.py",
        start: 18795381,
        end: 18795450
      }, {
        filename: "/lib/python3.15/test/archivetestdata/testtar.tar",
        start: 18795450,
        end: 19230650
      }, {
        filename: "/lib/python3.15/test/archivetestdata/testtar.tar.xz",
        start: 19230650,
        end: 19230822
      }, {
        filename: "/lib/python3.15/test/archivetestdata/zip_cp437_header.zip",
        start: 19230822,
        end: 19231092
      }, {
        filename: "/lib/python3.15/test/archivetestdata/zipdir.zip",
        start: 19231092,
        end: 19231466
      }, {
        filename: "/lib/python3.15/test/archivetestdata/zipdir_backslash.zip",
        start: 19231466,
        end: 19231658
      }, {
        filename: "/lib/python3.15/test/audiodata/pluck-pcm16.wav",
        start: 19231658,
        end: 19245028,
        audio: 1
      }, {
        filename: "/lib/python3.15/test/audiodata/pluck-pcm24-ext.wav",
        start: 19245028,
        end: 19264950,
        audio: 1
      }, {
        filename: "/lib/python3.15/test/audiodata/pluck-pcm24.wav",
        start: 19264950,
        end: 19284934,
        audio: 1
      }, {
        filename: "/lib/python3.15/test/audiodata/pluck-pcm32.wav",
        start: 19284934,
        end: 19311532,
        audio: 1
      }, {
        filename: "/lib/python3.15/test/audiodata/pluck-pcm8.wav",
        start: 19311532,
        end: 19318288,
        audio: 1
      }, {
        filename: "/lib/python3.15/test/audiotests.py",
        start: 19318288,
        end: 19330713
      }, {
        filename: "/lib/python3.15/test/audit-tests.py",
        start: 19330713,
        end: 19352677
      }, {
        filename: "/lib/python3.15/test/audit_test_data/__init__.py",
        start: 19352677,
        end: 19352677
      }, {
        filename: "/lib/python3.15/test/audit_test_data/submodule.py",
        start: 19352677,
        end: 19352677
      }, {
        filename: "/lib/python3.15/test/audit_test_data/submodule2.py",
        start: 19352677,
        end: 19352677
      }, {
        filename: "/lib/python3.15/test/autotest.py",
        start: 19352677,
        end: 19352891
      }, {
        filename: "/lib/python3.15/test/bisect_cmd.py",
        start: 19352891,
        end: 19358361
      }, {
        filename: "/lib/python3.15/test/certdata/allsans.pem",
        start: 19358361,
        end: 19368495
      }, {
        filename: "/lib/python3.15/test/certdata/badcert.pem",
        start: 19368495,
        end: 19370423
      }, {
        filename: "/lib/python3.15/test/certdata/badkey.pem",
        start: 19370423,
        end: 19372585
      }, {
        filename: "/lib/python3.15/test/certdata/capath/4e1295a3.0",
        start: 19372585,
        end: 19373399
      }, {
        filename: "/lib/python3.15/test/certdata/capath/5ed36f99.0",
        start: 19373399,
        end: 19375968
      }, {
        filename: "/lib/python3.15/test/certdata/capath/6e88d7b8.0",
        start: 19375968,
        end: 19376782
      }, {
        filename: "/lib/python3.15/test/certdata/capath/99d0fa06.0",
        start: 19376782,
        end: 19379351
      }, {
        filename: "/lib/python3.15/test/certdata/capath/b1930218.0",
        start: 19379351,
        end: 19380974
      }, {
        filename: "/lib/python3.15/test/certdata/capath/ceff1710.0",
        start: 19380974,
        end: 19382597
      }, {
        filename: "/lib/python3.15/test/certdata/cert3.pem",
        start: 19382597,
        end: 19384719
      }, {
        filename: "/lib/python3.15/test/certdata/ffdh3072.pem",
        start: 19384719,
        end: 19386931
      }, {
        filename: "/lib/python3.15/test/certdata/idnsans.pem",
        start: 19386931,
        end: 19396868
      }, {
        filename: "/lib/python3.15/test/certdata/keycert.passwd.pem",
        start: 19396868,
        end: 19401161
      }, {
        filename: "/lib/python3.15/test/certdata/keycert.pem",
        start: 19401161,
        end: 19405272
      }, {
        filename: "/lib/python3.15/test/certdata/keycert.pem.reference",
        start: 19405272,
        end: 19405881
      }, {
        filename: "/lib/python3.15/test/certdata/keycert2.pem",
        start: 19405881,
        end: 19410004
      }, {
        filename: "/lib/python3.15/test/certdata/keycert3.pem",
        start: 19410004,
        end: 19419443
      }, {
        filename: "/lib/python3.15/test/certdata/keycert3.pem.reference",
        start: 19419443,
        end: 19420193
      }, {
        filename: "/lib/python3.15/test/certdata/keycert4.pem",
        start: 19420193,
        end: 19429646
      }, {
        filename: "/lib/python3.15/test/certdata/keycertecc.pem",
        start: 19429646,
        end: 19435278
      }, {
        filename: "/lib/python3.15/test/certdata/leaf-missing-aki.ca.pem",
        start: 19435278,
        end: 19436026
      }, {
        filename: "/lib/python3.15/test/certdata/leaf-missing-aki.keycert.pem",
        start: 19436026,
        end: 19436997
      }, {
        filename: "/lib/python3.15/test/certdata/make_ssl_certs.py",
        start: 19436997,
        end: 19447369
      }, {
        filename: "/lib/python3.15/test/certdata/nokia.pem",
        start: 19447369,
        end: 19449292
      }, {
        filename: "/lib/python3.15/test/certdata/nosan.pem",
        start: 19449292,
        end: 19457376
      }, {
        filename: "/lib/python3.15/test/certdata/nullbytecert.pem",
        start: 19457376,
        end: 19462811
      }, {
        filename: "/lib/python3.15/test/certdata/nullcert.pem",
        start: 19462811,
        end: 19462811
      }, {
        filename: "/lib/python3.15/test/certdata/pycacert.pem",
        start: 19462811,
        end: 19468601
      }, {
        filename: "/lib/python3.15/test/certdata/pycakey.pem",
        start: 19468601,
        end: 19471085
      }, {
        filename: "/lib/python3.15/test/certdata/revocation.crl",
        start: 19471085,
        end: 19471889
      }, {
        filename: "/lib/python3.15/test/certdata/secp384r1.pem",
        start: 19471889,
        end: 19472145
      }, {
        filename: "/lib/python3.15/test/certdata/selfsigned_pythontestdotnet.pem",
        start: 19472145,
        end: 19474275
      }, {
        filename: "/lib/python3.15/test/certdata/ssl_cert.pem",
        start: 19474275,
        end: 19475902
      }, {
        filename: "/lib/python3.15/test/certdata/ssl_key.passwd.pem",
        start: 19475902,
        end: 19478568
      }, {
        filename: "/lib/python3.15/test/certdata/ssl_key.pem",
        start: 19478568,
        end: 19481052
      }, {
        filename: "/lib/python3.15/test/certdata/talos-2019-0758.pem",
        start: 19481052,
        end: 19482382
      }, {
        filename: "/lib/python3.15/test/cjkencodings/big5-utf8.txt",
        start: 19482382,
        end: 19482946
      }, {
        filename: "/lib/python3.15/test/cjkencodings/big5.txt",
        start: 19482946,
        end: 19483378
      }, {
        filename: "/lib/python3.15/test/cjkencodings/big5hkscs-utf8.txt",
        start: 19483378,
        end: 19483410
      }, {
        filename: "/lib/python3.15/test/cjkencodings/big5hkscs.txt",
        start: 19483410,
        end: 19483433
      }, {
        filename: "/lib/python3.15/test/cjkencodings/cp949-utf8.txt",
        start: 19483433,
        end: 19483911
      }, {
        filename: "/lib/python3.15/test/cjkencodings/cp949.txt",
        start: 19483911,
        end: 19484257
      }, {
        filename: "/lib/python3.15/test/cjkencodings/euc_jisx0213-utf8.txt",
        start: 19484257,
        end: 19485401
      }, {
        filename: "/lib/python3.15/test/cjkencodings/euc_jisx0213.txt",
        start: 19485401,
        end: 19486194
      }, {
        filename: "/lib/python3.15/test/cjkencodings/euc_jp-utf8.txt",
        start: 19486194,
        end: 19487288
      }, {
        filename: "/lib/python3.15/test/cjkencodings/euc_jp.txt",
        start: 19487288,
        end: 19488048
      }, {
        filename: "/lib/python3.15/test/cjkencodings/euc_kr-utf8.txt",
        start: 19488048,
        end: 19488634
      }, {
        filename: "/lib/python3.15/test/cjkencodings/euc_kr.txt",
        start: 19488634,
        end: 19489090
      }, {
        filename: "/lib/python3.15/test/cjkencodings/gb18030-utf8.txt",
        start: 19489090,
        end: 19490217
      }, {
        filename: "/lib/python3.15/test/cjkencodings/gb18030.txt",
        start: 19490217,
        end: 19491081
      }, {
        filename: "/lib/python3.15/test/cjkencodings/gb2312-utf8.txt",
        start: 19491081,
        end: 19491561
      }, {
        filename: "/lib/python3.15/test/cjkencodings/gb2312.txt",
        start: 19491561,
        end: 19491885
      }, {
        filename: "/lib/python3.15/test/cjkencodings/gbk-utf8.txt",
        start: 19491885,
        end: 19492928
      }, {
        filename: "/lib/python3.15/test/cjkencodings/gbk.txt",
        start: 19492928,
        end: 19493683
      }, {
        filename: "/lib/python3.15/test/cjkencodings/hz-utf8.txt",
        start: 19493683,
        end: 19493772
      }, {
        filename: "/lib/python3.15/test/cjkencodings/hz.txt",
        start: 19493772,
        end: 19493855
      }, {
        filename: "/lib/python3.15/test/cjkencodings/iso2022_jp-utf8.txt",
        start: 19493855,
        end: 19494949
      }, {
        filename: "/lib/python3.15/test/cjkencodings/iso2022_jp.txt",
        start: 19494949,
        end: 19495817
      }, {
        filename: "/lib/python3.15/test/cjkencodings/iso2022_kr-utf8.txt",
        start: 19495817,
        end: 19496380
      }, {
        filename: "/lib/python3.15/test/cjkencodings/iso2022_kr.txt",
        start: 19496380,
        end: 19496882
      }, {
        filename: "/lib/python3.15/test/cjkencodings/johab-utf8.txt",
        start: 19496882,
        end: 19497360
      }, {
        filename: "/lib/python3.15/test/cjkencodings/johab.txt",
        start: 19497360,
        end: 19497706
      }, {
        filename: "/lib/python3.15/test/cjkencodings/shift_jis-utf8.txt",
        start: 19497706,
        end: 19498800
      }, {
        filename: "/lib/python3.15/test/cjkencodings/shift_jis.txt",
        start: 19498800,
        end: 19499560
      }, {
        filename: "/lib/python3.15/test/cjkencodings/shift_jisx0213-utf8.txt",
        start: 19499560,
        end: 19500704
      }, {
        filename: "/lib/python3.15/test/cjkencodings/shift_jisx0213.txt",
        start: 19500704,
        end: 19501493
      }, {
        filename: "/lib/python3.15/test/clinic.test.c",
        start: 19501493,
        end: 19680291
      }, {
        filename: "/lib/python3.15/test/configdata/cfgparser.1",
        start: 19680291,
        end: 19680358
      }, {
        filename: "/lib/python3.15/test/configdata/cfgparser.2",
        start: 19680358,
        end: 19699830
      }, {
        filename: "/lib/python3.15/test/configdata/cfgparser.3",
        start: 19699830,
        end: 19701417
      }, {
        filename: "/lib/python3.15/test/cov.py",
        start: 19701417,
        end: 19702711
      }, {
        filename: "/lib/python3.15/test/crashers/README",
        start: 19702711,
        end: 19703541
      }, {
        filename: "/lib/python3.15/test/crashers/bogus_code_obj.py",
        start: 19703541,
        end: 19704107
      }, {
        filename: "/lib/python3.15/test/crashers/gc_inspection.py",
        start: 19704107,
        end: 19705199
      }, {
        filename: "/lib/python3.15/test/crashers/infinite_loop_re.py",
        start: 19705199,
        end: 19705852
      }, {
        filename: "/lib/python3.15/test/crashers/mutation_inside_cyclegc.py",
        start: 19705852,
        end: 19706605
      }, {
        filename: "/lib/python3.15/test/crashers/recursive_call.py",
        start: 19706605,
        end: 19706963
      }, {
        filename: "/lib/python3.15/test/crashers/trace_at_recursion_limit.py",
        start: 19706963,
        end: 19707339
      }, {
        filename: "/lib/python3.15/test/crashers/underlying_dict.py",
        start: 19707339,
        end: 19707621
      }, {
        filename: "/lib/python3.15/test/curses_tests.py",
        start: 19707621,
        end: 19708863
      }, {
        filename: "/lib/python3.15/test/data/README",
        start: 19708863,
        end: 19708992
      }, {
        filename: "/lib/python3.15/test/datetimetester.py",
        start: 19708992,
        end: 20013248
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/abs.decTest",
        start: 20013248,
        end: 20019538
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/add.decTest",
        start: 20019538,
        end: 20159876
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/and.decTest",
        start: 20159876,
        end: 20176240
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/base.decTest",
        start: 20176240,
        end: 20237595
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/clamp.decTest",
        start: 20237595,
        end: 20248604
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/class.decTest",
        start: 20248604,
        end: 20254980
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/compare.decTest",
        start: 20254980,
        end: 20284607
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/comparetotal.decTest",
        start: 20284607,
        end: 20319030
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/comparetotmag.decTest",
        start: 20319030,
        end: 20355159
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/copy.decTest",
        start: 20355159,
        end: 20358535
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/copyabs.decTest",
        start: 20358535,
        end: 20362019
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/copynegate.decTest",
        start: 20362019,
        end: 20365692
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/copysign.decTest",
        start: 20365692,
        end: 20373070
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/ddAbs.decTest",
        start: 20373070,
        end: 20377971
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/ddAdd.decTest",
        start: 20377971,
        end: 20456066
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/ddAnd.decTest",
        start: 20456066,
        end: 20474685
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/ddBase.decTest",
        start: 20474685,
        end: 20529142
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/ddCanonical.decTest",
        start: 20529142,
        end: 20548050
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/ddClass.decTest",
        start: 20548050,
        end: 20551957
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/ddCompare.decTest",
        start: 20551957,
        end: 20582239
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/ddCompareSig.decTest",
        start: 20582239,
        end: 20610647
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/ddCompareTotal.decTest",
        start: 20610647,
        end: 20641285
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/ddCompareTotalMag.decTest",
        start: 20641285,
        end: 20673703
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/ddCopy.decTest",
        start: 20673703,
        end: 20677324
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/ddCopyAbs.decTest",
        start: 20677324,
        end: 20681053
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/ddCopyNegate.decTest",
        start: 20681053,
        end: 20684935
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/ddCopySign.decTest",
        start: 20684935,
        end: 20692567
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/ddDivide.decTest",
        start: 20692567,
        end: 20740704
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/ddDivideInt.decTest",
        start: 20740704,
        end: 20760288
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/ddEncode.decTest",
        start: 20760288,
        end: 20784976
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/ddFMA.decTest",
        start: 20784976,
        end: 20887155
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/ddInvert.decTest",
        start: 20887155,
        end: 20897516
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/ddLogB.decTest",
        start: 20897516,
        end: 20903756
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/ddMax.decTest",
        start: 20903756,
        end: 20916070
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/ddMaxMag.decTest",
        start: 20916070,
        end: 20928813
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/ddMin.decTest",
        start: 20928813,
        end: 20940782
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/ddMinMag.decTest",
        start: 20940782,
        end: 20952407
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/ddMinus.decTest",
        start: 20952407,
        end: 20956197
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/ddMultiply.decTest",
        start: 20956197,
        end: 20985501
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/ddNextMinus.decTest",
        start: 20985501,
        end: 20992328
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/ddNextPlus.decTest",
        start: 20992328,
        end: 20999051
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/ddNextToward.decTest",
        start: 20999051,
        end: 21024041
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/ddOr.decTest",
        start: 21024041,
        end: 21040064
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/ddPlus.decTest",
        start: 21040064,
        end: 21043810
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/ddQuantize.decTest",
        start: 21043810,
        end: 21086305
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/ddReduce.decTest",
        start: 21086305,
        end: 21093765
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/ddRemainder.decTest",
        start: 21093765,
        end: 21120754
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/ddRemainderNear.decTest",
        start: 21120754,
        end: 21151015
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/ddRotate.decTest",
        start: 21151015,
        end: 21165097
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/ddSameQuantum.decTest",
        start: 21165097,
        end: 21182638
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/ddScaleB.decTest",
        start: 21182638,
        end: 21195425
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/ddShift.decTest",
        start: 21195425,
        end: 21208836
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/ddSubtract.decTest",
        start: 21208836,
        end: 21244234
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/ddToIntegral.decTest",
        start: 21244234,
        end: 21256426
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/ddXor.decTest",
        start: 21256426,
        end: 21274128
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/decDouble.decTest",
        start: 21274128,
        end: 21276337
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/decQuad.decTest",
        start: 21276337,
        end: 21278544
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/decSingle.decTest",
        start: 21278544,
        end: 2128e4
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/divide.decTest",
        start: 2128e4,
        end: 21317804
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/divideint.decTest",
        start: 21317804,
        end: 21338240
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/dqAbs.decTest",
        start: 21338240,
        end: 21343515
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/dqAdd.decTest",
        start: 21343515,
        end: 21432712
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/dqAnd.decTest",
        start: 21432712,
        end: 21461835
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/dqBase.decTest",
        start: 21461835,
        end: 21520790
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/dqCanonical.decTest",
        start: 21520790,
        end: 21548109
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/dqClass.decTest",
        start: 21548109,
        end: 21552129
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/dqCompare.decTest",
        start: 21552129,
        end: 21585251
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/dqCompareSig.decTest",
        start: 21585251,
        end: 21614946
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/dqCompareTotal.decTest",
        start: 21614946,
        end: 21645792
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/dqCompareTotalMag.decTest",
        start: 21645792,
        end: 21678418
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/dqCopy.decTest",
        start: 21678418,
        end: 21682405
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/dqCopyAbs.decTest",
        start: 21682405,
        end: 21686506
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/dqCopyNegate.decTest",
        start: 21686506,
        end: 21690754
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/dqCopySign.decTest",
        start: 21690754,
        end: 21698982
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/dqDivide.decTest",
        start: 21698982,
        end: 21754084
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/dqDivideInt.decTest",
        start: 21754084,
        end: 21773910
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/dqEncode.decTest",
        start: 21773910,
        end: 21805340
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/dqFMA.decTest",
        start: 21805340,
        end: 21935330
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/dqInvert.decTest",
        start: 21935330,
        end: 21951454
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/dqLogB.decTest",
        start: 21951454,
        end: 21957834
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/dqMax.decTest",
        start: 21957834,
        end: 21970183
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/dqMaxMag.decTest",
        start: 21970183,
        end: 21982972
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/dqMin.decTest",
        start: 21982972,
        end: 21994976
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/dqMinMag.decTest",
        start: 21994976,
        end: 22006625
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/dqMinus.decTest",
        start: 22006625,
        end: 22010781
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/dqMultiply.decTest",
        start: 22010781,
        end: 22043274
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/dqNextMinus.decTest",
        start: 22043274,
        end: 22051925
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/dqNextPlus.decTest",
        start: 22051925,
        end: 22060452
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/dqNextToward.decTest",
        start: 22060452,
        end: 22090178
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/dqOr.decTest",
        start: 22090178,
        end: 22120795
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/dqPlus.decTest",
        start: 22120795,
        end: 22124907
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/dqQuantize.decTest",
        start: 22124907,
        end: 22167999
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/dqReduce.decTest",
        start: 22167999,
        end: 22175819
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/dqRemainder.decTest",
        start: 22175819,
        end: 22203384
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/dqRemainderNear.decTest",
        start: 22203384,
        end: 22234675
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/dqRotate.decTest",
        start: 22234675,
        end: 22255655
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/dqSameQuantum.decTest",
        start: 22255655,
        end: 22273800
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/dqScaleB.decTest",
        start: 22273800,
        end: 22289859
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/dqShift.decTest",
        start: 22289859,
        end: 22309295
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/dqSubtract.decTest",
        start: 22309295,
        end: 22351223
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/dqToIntegral.decTest",
        start: 22351223,
        end: 22363447
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/dqXor.decTest",
        start: 22363447,
        end: 22391710
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/dsBase.decTest",
        start: 22391710,
        end: 22441276
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/dsEncode.decTest",
        start: 22441276,
        end: 22457162
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/exp.decTest",
        start: 22457162,
        end: 22496602
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/extra.decTest",
        start: 22496602,
        end: 22589115
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/fma.decTest",
        start: 22589115,
        end: 22784441
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/inexact.decTest",
        start: 22784441,
        end: 22794933
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/invert.decTest",
        start: 22794933,
        end: 22803219
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/ln.decTest",
        start: 22803219,
        end: 22838744
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/log10.decTest",
        start: 22838744,
        end: 22871440
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/logb.decTest",
        start: 22871440,
        end: 22878759
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/max.decTest",
        start: 22878759,
        end: 22894731
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/maxmag.decTest",
        start: 22894731,
        end: 22912083
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/min.decTest",
        start: 22912083,
        end: 22927773
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/minmag.decTest",
        start: 22927773,
        end: 22943211
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/minus.decTest",
        start: 22943211,
        end: 22950636
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/multiply.decTest",
        start: 22950636,
        end: 22988950
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/nextminus.decTest",
        start: 22988950,
        end: 22995892
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/nextplus.decTest",
        start: 22995892,
        end: 23002815
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/nexttoward.decTest",
        start: 23002815,
        end: 23028039
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/or.decTest",
        start: 23028039,
        end: 23043896
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/plus.decTest",
        start: 23043896,
        end: 23051778
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/power.decTest",
        start: 23051778,
        end: 23146759
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/powersqrt.decTest",
        start: 23146759,
        end: 23305414
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/quantize.decTest",
        start: 23305414,
        end: 23352696
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/randomBound32.decTest",
        start: 23352696,
        end: 23657202
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/randoms.decTest",
        start: 23657202,
        end: 23948275
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/reduce.decTest",
        start: 23948275,
        end: 23957594
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/remainder.decTest",
        start: 23957594,
        end: 23984720
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/remainderNear.decTest",
        start: 23984720,
        end: 24009740
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/rescale.decTest",
        start: 24009740,
        end: 24044997
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/rotate.decTest",
        start: 24044997,
        end: 24056885
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/rounding.decTest",
        start: 24056885,
        end: 24120657
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/samequantum.decTest",
        start: 24120657,
        end: 24136859
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/scaleb.decTest",
        start: 24136859,
        end: 24146771
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/shift.decTest",
        start: 24146771,
        end: 24158443
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/squareroot.decTest",
        start: 24158443,
        end: 24350902
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/subtract.decTest",
        start: 24350902,
        end: 24395207
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/testall.decTest",
        start: 24395207,
        end: 24397938
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/tointegral.decTest",
        start: 24397938,
        end: 24406802
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/tointegralx.decTest",
        start: 24406802,
        end: 24418662
      }, {
        filename: "/lib/python3.15/test/decimaltestdata/xor.decTest",
        start: 24418662,
        end: 24434991
      }, {
        filename: "/lib/python3.15/test/dis_module.py",
        start: 24434991,
        end: 24435067
      }, {
        filename: "/lib/python3.15/test/dtracedata/assert_usable.d",
        start: 24435067,
        end: 24435122
      }, {
        filename: "/lib/python3.15/test/dtracedata/assert_usable.stp",
        start: 24435122,
        end: 24435176
      }, {
        filename: "/lib/python3.15/test/dtracedata/call_stack.d",
        start: 24435176,
        end: 24435833
      }, {
        filename: "/lib/python3.15/test/dtracedata/call_stack.d.expected",
        start: 24435833,
        end: 24436630
      }, {
        filename: "/lib/python3.15/test/dtracedata/call_stack.py",
        start: 24436630,
        end: 24437122
      }, {
        filename: "/lib/python3.15/test/dtracedata/call_stack.stp",
        start: 24437122,
        end: 24437929
      }, {
        filename: "/lib/python3.15/test/dtracedata/call_stack.stp.expected",
        start: 24437929,
        end: 24438535
      }, {
        filename: "/lib/python3.15/test/dtracedata/gc.d",
        start: 24438535,
        end: 24438832
      }, {
        filename: "/lib/python3.15/test/dtracedata/gc.d.expected",
        start: 24438832,
        end: 24438916
      }, {
        filename: "/lib/python3.15/test/dtracedata/gc.py",
        start: 24438916,
        end: 24439071
      }, {
        filename: "/lib/python3.15/test/dtracedata/gc.stp",
        start: 24439071,
        end: 24439515
      }, {
        filename: "/lib/python3.15/test/dtracedata/gc.stp.expected",
        start: 24439515,
        end: 24439607
      }, {
        filename: "/lib/python3.15/test/dtracedata/instance.py",
        start: 24439607,
        end: 24439924
      }, {
        filename: "/lib/python3.15/test/dtracedata/line.d",
        start: 24439924,
        end: 24440103
      }, {
        filename: "/lib/python3.15/test/dtracedata/line.d.expected",
        start: 24440103,
        end: 24440609
      }, {
        filename: "/lib/python3.15/test/dtracedata/line.py",
        start: 24440609,
        end: 24440902
      }, {
        filename: "/lib/python3.15/test/empty.vbs",
        start: 24440902,
        end: 24440972
      }, {
        filename: "/lib/python3.15/test/encoded_modules/__init__.py",
        start: 24440972,
        end: 24442246
      }, {
        filename: "/lib/python3.15/test/encoded_modules/module_iso_8859_1.py",
        start: 24442246,
        end: 24442484
      }, {
        filename: "/lib/python3.15/test/encoded_modules/module_koi8_r.py",
        start: 24442484,
        end: 24442597
      }, {
        filename: "/lib/python3.15/test/exception_hierarchy.txt",
        start: 24442597,
        end: 24445031
      }, {
        filename: "/lib/python3.15/test/fork_wait.py",
        start: 24445031,
        end: 24447380
      }, {
        filename: "/lib/python3.15/test/leakers/README.txt",
        start: 24447380,
        end: 24448470
      }, {
        filename: "/lib/python3.15/test/leakers/__init__.py",
        start: 24448470,
        end: 24448470
      }, {
        filename: "/lib/python3.15/test/leakers/test_ctypes.py",
        start: 24448470,
        end: 24448804
      }, {
        filename: "/lib/python3.15/test/leakers/test_selftype.py",
        start: 24448804,
        end: 24449097
      }, {
        filename: "/lib/python3.15/test/levenshtein_examples.json",
        start: 24449097,
        end: 24865288
      }, {
        filename: "/lib/python3.15/test/libregrtest/__init__.py",
        start: 24865288,
        end: 24865288
      }, {
        filename: "/lib/python3.15/test/libregrtest/cmdline.py",
        start: 24865288,
        end: 24891187
      }, {
        filename: "/lib/python3.15/test/libregrtest/filter.py",
        start: 24891187,
        end: 24893640
      }, {
        filename: "/lib/python3.15/test/libregrtest/findtests.py",
        start: 24893640,
        end: 24897409
      }, {
        filename: "/lib/python3.15/test/libregrtest/logger.py",
        start: 24897409,
        end: 24900238
      }, {
        filename: "/lib/python3.15/test/libregrtest/main.py",
        start: 24900238,
        end: 24929336
      }, {
        filename: "/lib/python3.15/test/libregrtest/mypy.ini",
        start: 24929336,
        end: 24930136
      }, {
        filename: "/lib/python3.15/test/libregrtest/parallel_case.py",
        start: 24930136,
        end: 24932914
      }, {
        filename: "/lib/python3.15/test/libregrtest/pgo.py",
        start: 24932914,
        end: 24934298
      }, {
        filename: "/lib/python3.15/test/libregrtest/refleak.py",
        start: 24934298,
        end: 24944555
      }, {
        filename: "/lib/python3.15/test/libregrtest/result.py",
        start: 24944555,
        end: 24952848
      }, {
        filename: "/lib/python3.15/test/libregrtest/results.py",
        start: 24952848,
        end: 24963705
      }, {
        filename: "/lib/python3.15/test/libregrtest/run_workers.py",
        start: 24963705,
        end: 24986705
      }, {
        filename: "/lib/python3.15/test/libregrtest/runtests.py",
        start: 24986705,
        end: 24994032
      }, {
        filename: "/lib/python3.15/test/libregrtest/save_env.py",
        start: 24994032,
        end: 25007986
      }, {
        filename: "/lib/python3.15/test/libregrtest/setup.py",
        start: 25007986,
        end: 25013891
      }, {
        filename: "/lib/python3.15/test/libregrtest/single.py",
        start: 25013891,
        end: 25026118
      }, {
        filename: "/lib/python3.15/test/libregrtest/testresult.py",
        start: 25026118,
        end: 25032469
      }, {
        filename: "/lib/python3.15/test/libregrtest/tsan.py",
        start: 25032469,
        end: 25033747
      }, {
        filename: "/lib/python3.15/test/libregrtest/utils.py",
        start: 25033747,
        end: 25057112
      }, {
        filename: "/lib/python3.15/test/libregrtest/win_utils.py",
        start: 25057112,
        end: 25061783
      }, {
        filename: "/lib/python3.15/test/libregrtest/worker.py",
        start: 25061783,
        end: 25066264
      }, {
        filename: "/lib/python3.15/test/list_tests.py",
        start: 25066264,
        end: 25083896
      }, {
        filename: "/lib/python3.15/test/lock_tests.py",
        start: 25083896,
        end: 25122213
      }, {
        filename: "/lib/python3.15/test/mapping_tests.py",
        start: 25122213,
        end: 25144727
      }, {
        filename: "/lib/python3.15/test/mathdata/cmath_testcases.txt",
        start: 25144727,
        end: 25289398
      }, {
        filename: "/lib/python3.15/test/mathdata/floating_points.txt",
        start: 25289398,
        end: 25305700
      }, {
        filename: "/lib/python3.15/test/mathdata/formatfloat_testcases.txt",
        start: 25305700,
        end: 25313330
      }, {
        filename: "/lib/python3.15/test/mathdata/ieee754.txt",
        start: 25313330,
        end: 25316701
      }, {
        filename: "/lib/python3.15/test/mathdata/math_testcases.txt",
        start: 25316701,
        end: 25340443
      }, {
        filename: "/lib/python3.15/test/memory_watchdog.py",
        start: 25340443,
        end: 25341154
      }, {
        filename: "/lib/python3.15/test/mime.types",
        start: 25341154,
        end: 25389663
      }, {
        filename: "/lib/python3.15/test/mock_socket.py",
        start: 25389663,
        end: 25393438
      }, {
        filename: "/lib/python3.15/test/mp_fork_bomb.py",
        start: 25393438,
        end: 25393886
      }, {
        filename: "/lib/python3.15/test/mp_preload.py",
        start: 25393886,
        end: 25394237
      }, {
        filename: "/lib/python3.15/test/mp_preload_flush.py",
        start: 25394237,
        end: 25394528
      }, {
        filename: "/lib/python3.15/test/mp_preload_main.py",
        start: 25394528,
        end: 25394815
      }, {
        filename: "/lib/python3.15/test/multibytecodec_support.py",
        start: 25394815,
        end: 25410078
      }, {
        filename: "/lib/python3.15/test/pickletester.py",
        start: 25410078,
        end: 25616051
      }, {
        filename: "/lib/python3.15/test/profilee.py",
        start: 25616051,
        end: 25619092
      }, {
        filename: "/lib/python3.15/test/pstats.pck",
        start: 25619092,
        end: 25685699
      }, {
        filename: "/lib/python3.15/test/pyclbr_input.py",
        start: 25685699,
        end: 25687368
      }, {
        filename: "/lib/python3.15/test/pythoninfo.py",
        start: 25687368,
        end: 25717220
      }, {
        filename: "/lib/python3.15/test/randv2_32.pck",
        start: 25717220,
        end: 25724737
      }, {
        filename: "/lib/python3.15/test/randv2_64.pck",
        start: 25724737,
        end: 25732102
      }, {
        filename: "/lib/python3.15/test/randv3.pck",
        start: 25732102,
        end: 25740106
      }, {
        filename: "/lib/python3.15/test/re_tests.py",
        start: 25740106,
        end: 25766658
      }, {
        filename: "/lib/python3.15/test/regrtest.py",
        start: 25766658,
        end: 25767958
      }, {
        filename: "/lib/python3.15/test/regrtestdata/import_from_tests/test_regrtest_a.py",
        start: 25767958,
        end: 25768374
      }, {
        filename: "/lib/python3.15/test/regrtestdata/import_from_tests/test_regrtest_b/__init__.py",
        start: 25768374,
        end: 25768683
      }, {
        filename: "/lib/python3.15/test/regrtestdata/import_from_tests/test_regrtest_b/util.py",
        start: 25768683,
        end: 25768683
      }, {
        filename: "/lib/python3.15/test/regrtestdata/import_from_tests/test_regrtest_c.py",
        start: 25768683,
        end: 25769099
      }, {
        filename: "/lib/python3.15/test/relimport.py",
        start: 25769099,
        end: 25769126
      }, {
        filename: "/lib/python3.15/test/seq_tests.py",
        start: 25769126,
        end: 25784443
      }, {
        filename: "/lib/python3.15/test/signalinterproctester.py",
        start: 25784443,
        end: 25787640
      }, {
        filename: "/lib/python3.15/test/ssl_servers.py",
        start: 25787640,
        end: 25794931
      }, {
        filename: "/lib/python3.15/test/ssltests.py",
        start: 25794931,
        end: 25795966
      }, {
        filename: "/lib/python3.15/test/string_tests.py",
        start: 25795966,
        end: 25869979
      }, {
        filename: "/lib/python3.15/test/subprocessdata/fd_status.py",
        start: 25869979,
        end: 25870837
      }, {
        filename: "/lib/python3.15/test/subprocessdata/input_reader.py",
        start: 25870837,
        end: 25870967
      }, {
        filename: "/lib/python3.15/test/subprocessdata/qcat.py",
        start: 25870967,
        end: 25871126
      }, {
        filename: "/lib/python3.15/test/subprocessdata/qgrep.py",
        start: 25871126,
        end: 25871379
      }, {
        filename: "/lib/python3.15/test/subprocessdata/sigchild_ignore.py",
        start: 25871379,
        end: 25872136
      }, {
        filename: "/lib/python3.15/test/support/__init__.py",
        start: 25872136,
        end: 25979143
      }, {
        filename: "/lib/python3.15/test/support/_hypothesis_stubs/__init__.py",
        start: 25979143,
        end: 25981907
      }, {
        filename: "/lib/python3.15/test/support/_hypothesis_stubs/_helpers.py",
        start: 25981907,
        end: 25983205
      }, {
        filename: "/lib/python3.15/test/support/_hypothesis_stubs/strategies.py",
        start: 25983205,
        end: 25985062
      }, {
        filename: "/lib/python3.15/test/support/ast_helper.py",
        start: 25985062,
        end: 25987060
      }, {
        filename: "/lib/python3.15/test/support/asynchat.py",
        start: 25987060,
        end: 25998663
      }, {
        filename: "/lib/python3.15/test/support/asyncore.py",
        start: 25998663,
        end: 26019045
      }, {
        filename: "/lib/python3.15/test/support/bytecode_helper.py",
        start: 26019045,
        end: 26024807
      }, {
        filename: "/lib/python3.15/test/support/channels.py",
        start: 26024807,
        end: 26033347
      }, {
        filename: "/lib/python3.15/test/support/hashlib_helper.py",
        start: 26033347,
        end: 26072067
      }, {
        filename: "/lib/python3.15/test/support/hypothesis_helper.py",
        start: 26072067,
        end: 26074159
      }, {
        filename: "/lib/python3.15/test/support/i18n_helper.py",
        start: 26074159,
        end: 26076190
      }, {
        filename: "/lib/python3.15/test/support/import_helper.py",
        start: 26076190,
        end: 26090909
      }, {
        filename: "/lib/python3.15/test/support/logging_helper.py",
        start: 26090909,
        end: 26091825
      }, {
        filename: "/lib/python3.15/test/support/numbers.py",
        start: 26091825,
        end: 26093364
      }, {
        filename: "/lib/python3.15/test/support/os_helper.py",
        start: 26093364,
        end: 26119290
      }, {
        filename: "/lib/python3.15/test/support/pty_helper.py",
        start: 26119290,
        end: 26122590
      }, {
        filename: "/lib/python3.15/test/support/refleak_helper.py",
        start: 26122590,
        end: 26122755
      }, {
        filename: "/lib/python3.15/test/support/script_helper.py",
        start: 26122755,
        end: 26135395
      }, {
        filename: "/lib/python3.15/test/support/smtpd.py",
        start: 26135395,
        end: 26166205
      }, {
        filename: "/lib/python3.15/test/support/socket_helper.py",
        start: 26166205,
        end: 26179985
      }, {
        filename: "/lib/python3.15/test/support/strace_helper.py",
        start: 26179985,
        end: 26187117
      }, {
        filename: "/lib/python3.15/test/support/testcase.py",
        start: 26187117,
        end: 26189485
      }, {
        filename: "/lib/python3.15/test/support/threading_helper.py",
        start: 26189485,
        end: 26198265
      }, {
        filename: "/lib/python3.15/test/support/venv.py",
        start: 26198265,
        end: 26200915
      }, {
        filename: "/lib/python3.15/test/support/warnings_helper.py",
        start: 26200915,
        end: 26208042
      }, {
        filename: "/lib/python3.15/test/test___all__.py",
        start: 26208042,
        end: 26213255
      }, {
        filename: "/lib/python3.15/test/test__colorize.py",
        start: 26213255,
        end: 26221371
      }, {
        filename: "/lib/python3.15/test/test__interpchannels.py",
        start: 26221371,
        end: 26284748
      }, {
        filename: "/lib/python3.15/test/test__interpreters.py",
        start: 26284748,
        end: 26319728
      }, {
        filename: "/lib/python3.15/test/test__locale.py",
        start: 26319728,
        end: 26332468
      }, {
        filename: "/lib/python3.15/test/test__opcode.py",
        start: 26332468,
        end: 26338610
      }, {
        filename: "/lib/python3.15/test/test__osx_support.py",
        start: 26338610,
        end: 26352457
      }, {
        filename: "/lib/python3.15/test/test_abc.py",
        start: 26352457,
        end: 26376823
      }, {
        filename: "/lib/python3.15/test/test_abstract_numbers.py",
        start: 26376823,
        end: 26382695
      }, {
        filename: "/lib/python3.15/test/test_android.py",
        start: 26382695,
        end: 26401348
      }, {
        filename: "/lib/python3.15/test/test_annotationlib.py",
        start: 26401348,
        end: 26477631
      }, {
        filename: "/lib/python3.15/test/test_apple.py",
        start: 26477631,
        end: 26482393
      }, {
        filename: "/lib/python3.15/test/test_argparse.py",
        start: 26482393,
        end: 26759298
      }, {
        filename: "/lib/python3.15/test/test_array.py",
        start: 26759298,
        end: 26818185
      }, {
        filename: "/lib/python3.15/test/test_asdl_parser.py",
        start: 26818185,
        end: 26822804
      }, {
        filename: "/lib/python3.15/test/test_ast/__init__.py",
        start: 26822804,
        end: 26822937
      }, {
        filename: "/lib/python3.15/test/test_ast/data/ast_repr.txt",
        start: 26822937,
        end: 26855640
      }, {
        filename: "/lib/python3.15/test/test_ast/snippets.py",
        start: 26855640,
        end: 26911082
      }, {
        filename: "/lib/python3.15/test/test_ast/test_ast.py",
        start: 26911082,
        end: 27056547
      }, {
        filename: "/lib/python3.15/test/test_ast/utils.py",
        start: 27056547,
        end: 27057167
      }, {
        filename: "/lib/python3.15/test/test_asyncgen.py",
        start: 27057167,
        end: 27116860
      }, {
        filename: "/lib/python3.15/test/test_asyncio/__init__.py",
        start: 27116860,
        end: 27117213
      }, {
        filename: "/lib/python3.15/test/test_asyncio/__main__.py",
        start: 27117213,
        end: 27117271
      }, {
        filename: "/lib/python3.15/test/test_asyncio/echo.py",
        start: 27117271,
        end: 27117419
      }, {
        filename: "/lib/python3.15/test/test_asyncio/echo2.py",
        start: 27117419,
        end: 27117542
      }, {
        filename: "/lib/python3.15/test/test_asyncio/echo3.py",
        start: 27117542,
        end: 27117818
      }, {
        filename: "/lib/python3.15/test/test_asyncio/functional.py",
        start: 27117818,
        end: 27125252
      }, {
        filename: "/lib/python3.15/test/test_asyncio/test_base_events.py",
        start: 27125252,
        end: 27214122
      }, {
        filename: "/lib/python3.15/test/test_asyncio/test_buffered_proto.py",
        start: 27214122,
        end: 27216467
      }, {
        filename: "/lib/python3.15/test/test_asyncio/test_context.py",
        start: 27216467,
        end: 27217544
      }, {
        filename: "/lib/python3.15/test/test_asyncio/test_eager_task_factory.py",
        start: 27217544,
        end: 27234447
      }, {
        filename: "/lib/python3.15/test/test_asyncio/test_events.py",
        start: 27234447,
        end: 27351933
      }, {
        filename: "/lib/python3.15/test/test_asyncio/test_free_threading.py",
        start: 27351933,
        end: 27359711
      }, {
        filename: "/lib/python3.15/test/test_asyncio/test_futures.py",
        start: 27359711,
        end: 27399227
      }, {
        filename: "/lib/python3.15/test/test_asyncio/test_futures2.py",
        start: 27399227,
        end: 27402067
      }, {
        filename: "/lib/python3.15/test/test_asyncio/test_graph.py",
        start: 27402067,
        end: 27414873
      }, {
        filename: "/lib/python3.15/test/test_asyncio/test_locks.py",
        start: 27414873,
        end: 27469884
      }, {
        filename: "/lib/python3.15/test/test_asyncio/test_pep492.py",
        start: 27469884,
        end: 27475456
      }, {
        filename: "/lib/python3.15/test/test_asyncio/test_proactor_events.py",
        start: 27475456,
        end: 27515079
      }, {
        filename: "/lib/python3.15/test/test_asyncio/test_protocols.py",
        start: 27515079,
        end: 27517357
      }, {
        filename: "/lib/python3.15/test/test_asyncio/test_queues.py",
        start: 27517357,
        end: 27538413
      }, {
        filename: "/lib/python3.15/test/test_asyncio/test_runners.py",
        start: 27538413,
        end: 27554208
      }, {
        filename: "/lib/python3.15/test/test_asyncio/test_selector_events.py",
        start: 27554208,
        end: 27614313
      }, {
        filename: "/lib/python3.15/test/test_asyncio/test_sendfile.py",
        start: 27614313,
        end: 27635774
      }, {
        filename: "/lib/python3.15/test/test_asyncio/test_server.py",
        start: 27635774,
        end: 27647259
      }, {
        filename: "/lib/python3.15/test/test_asyncio/test_sock_lowlevel.py",
        start: 27647259,
        end: 27672476
      }, {
        filename: "/lib/python3.15/test/test_asyncio/test_ssl.py",
        start: 27672476,
        end: 27733254
      }, {
        filename: "/lib/python3.15/test/test_asyncio/test_sslproto.py",
        start: 27733254,
        end: 27762420
      }, {
        filename: "/lib/python3.15/test/test_asyncio/test_staggered.py",
        start: 27762420,
        end: 27766820
      }, {
        filename: "/lib/python3.15/test/test_asyncio/test_streams.py",
        start: 27766820,
        end: 27812799
      }, {
        filename: "/lib/python3.15/test/test_asyncio/test_subprocess.py",
        start: 27812799,
        end: 27848698
      }, {
        filename: "/lib/python3.15/test/test_asyncio/test_taskgroups.py",
        start: 27848698,
        end: 27881174
      }, {
        filename: "/lib/python3.15/test/test_asyncio/test_tasks.py",
        start: 27881174,
        end: 28006484
      }, {
        filename: "/lib/python3.15/test/test_asyncio/test_threads.py",
        start: 28006484,
        end: 28008153
      }, {
        filename: "/lib/python3.15/test/test_asyncio/test_timeouts.py",
        start: 28008153,
        end: 28023428
      }, {
        filename: "/lib/python3.15/test/test_asyncio/test_tools.py",
        start: 28023428,
        end: 28087890
      }, {
        filename: "/lib/python3.15/test/test_asyncio/test_transports.py",
        start: 28087890,
        end: 28091714
      }, {
        filename: "/lib/python3.15/test/test_asyncio/test_unix_events.py",
        start: 28091714,
        end: 28140032
      }, {
        filename: "/lib/python3.15/test/test_asyncio/test_waitfor.py",
        start: 28140032,
        end: 28150860
      }, {
        filename: "/lib/python3.15/test/test_asyncio/test_windows_events.py",
        start: 28150860,
        end: 28163409
      }, {
        filename: "/lib/python3.15/test/test_asyncio/test_windows_utils.py",
        start: 28163409,
        end: 28167643
      }, {
        filename: "/lib/python3.15/test/test_asyncio/utils.py",
        start: 28167643,
        end: 28185343
      }, {
        filename: "/lib/python3.15/test/test_atexit.py",
        start: 28185343,
        end: 28192696
      }, {
        filename: "/lib/python3.15/test/test_audit.py",
        start: 28192696,
        end: 28204101
      }, {
        filename: "/lib/python3.15/test/test_augassign.py",
        start: 28204101,
        end: 28211969
      }, {
        filename: "/lib/python3.15/test/test_base64.py",
        start: 28211969,
        end: 28259567
      }, {
        filename: "/lib/python3.15/test/test_baseexception.py",
        start: 28259567,
        end: 28267552
      }, {
        filename: "/lib/python3.15/test/test_bdb.py",
        start: 28267552,
        end: 28313267
      }, {
        filename: "/lib/python3.15/test/test_bigaddrspace.py",
        start: 28313267,
        end: 28316165
      }, {
        filename: "/lib/python3.15/test/test_bigmem.py",
        start: 28316165,
        end: 28363073
      }, {
        filename: "/lib/python3.15/test/test_binascii.py",
        start: 28363073,
        end: 28385743
      }, {
        filename: "/lib/python3.15/test/test_binop.py",
        start: 28385743,
        end: 28400216
      }, {
        filename: "/lib/python3.15/test/test_bisect.py",
        start: 28400216,
        end: 28417240
      }, {
        filename: "/lib/python3.15/test/test_bool.py",
        start: 28417240,
        end: 28431922
      }, {
        filename: "/lib/python3.15/test/test_buffer.py",
        start: 28431922,
        end: 28609716
      }, {
        filename: "/lib/python3.15/test/test_build_details.py",
        start: 28609716,
        end: 28618465
      }, {
        filename: "/lib/python3.15/test/test_builtin.py",
        start: 28618465,
        end: 28732786
      }, {
        filename: "/lib/python3.15/test/test_bytes.py",
        start: 28732786,
        end: 28840230
      }, {
        filename: "/lib/python3.15/test/test_bz2.py",
        start: 28840230,
        end: 28886562
      }, {
        filename: "/lib/python3.15/test/test_c_locale_coercion.py",
        start: 28886562,
        end: 28908468
      }, {
        filename: "/lib/python3.15/test/test_calendar.py",
        start: 28908468,
        end: 28972796
      }, {
        filename: "/lib/python3.15/test/test_call.py",
        start: 28972796,
        end: 29014974
      }, {
        filename: "/lib/python3.15/test/test_capi/__init__.py",
        start: 29014974,
        end: 29015263
      }, {
        filename: "/lib/python3.15/test/test_capi/__main__.py",
        start: 29015263,
        end: 29015312
      }, {
        filename: "/lib/python3.15/test/test_capi/check_config.py",
        start: 29015312,
        end: 29017934
      }, {
        filename: "/lib/python3.15/test/test_capi/test_abstract.py",
        start: 29017934,
        end: 29063781
      }, {
        filename: "/lib/python3.15/test/test_capi/test_bytearray.py",
        start: 29063781,
        end: 29071029
      }, {
        filename: "/lib/python3.15/test/test_capi/test_bytes.py",
        start: 29071029,
        end: 29087482
      }, {
        filename: "/lib/python3.15/test/test_capi/test_codecs.py",
        start: 29087482,
        end: 29130852
      }, {
        filename: "/lib/python3.15/test/test_capi/test_complex.py",
        start: 29130852,
        end: 29141718
      }, {
        filename: "/lib/python3.15/test/test_capi/test_config.py",
        start: 29141718,
        end: 29158432
      }, {
        filename: "/lib/python3.15/test/test_capi/test_dict.py",
        start: 29158432,
        end: 29180274
      }, {
        filename: "/lib/python3.15/test/test_capi/test_emscripten.py",
        start: 29180274,
        end: 29181123
      }, {
        filename: "/lib/python3.15/test/test_capi/test_eval.py",
        start: 29181123,
        end: 29184642
      }, {
        filename: "/lib/python3.15/test/test_capi/test_eval_code_ex.py",
        start: 29184642,
        end: 29189321
      }, {
        filename: "/lib/python3.15/test/test_capi/test_exceptions.py",
        start: 29189321,
        end: 29216433
      }, {
        filename: "/lib/python3.15/test/test_capi/test_file.py",
        start: 29216433,
        end: 29227986
      }, {
        filename: "/lib/python3.15/test/test_capi/test_float.py",
        start: 29227986,
        end: 29238263
      }, {
        filename: "/lib/python3.15/test/test_capi/test_frame.py",
        start: 29238263,
        end: 29240167
      }, {
        filename: "/lib/python3.15/test/test_capi/test_function.py",
        start: 29240167,
        end: 29252166
      }, {
        filename: "/lib/python3.15/test/test_capi/test_getargs.py",
        start: 29252166,
        end: 29315201
      }, {
        filename: "/lib/python3.15/test/test_capi/test_hash.py",
        start: 29315201,
        end: 29318267
      }, {
        filename: "/lib/python3.15/test/test_capi/test_immortal.py",
        start: 29318267,
        end: 29319861
      }, {
        filename: "/lib/python3.15/test/test_capi/test_import.py",
        start: 29319861,
        end: 29336061
      }, {
        filename: "/lib/python3.15/test/test_capi/test_list.py",
        start: 29336061,
        end: 29348704
      }, {
        filename: "/lib/python3.15/test/test_capi/test_long.py",
        start: 29348704,
        end: 29383750
      }, {
        filename: "/lib/python3.15/test/test_capi/test_mem.py",
        start: 29383750,
        end: 29391291
      }, {
        filename: "/lib/python3.15/test/test_capi/test_misc.py",
        start: 29391291,
        end: 29507435
      }, {
        filename: "/lib/python3.15/test/test_capi/test_modsupport.py",
        start: 29507435,
        end: 29513836
      }, {
        filename: "/lib/python3.15/test/test_capi/test_module.py",
        start: 29513836,
        end: 29521420
      }, {
        filename: "/lib/python3.15/test/test_capi/test_number.py",
        start: 29521420,
        end: 29535447
      }, {
        filename: "/lib/python3.15/test/test_capi/test_object.py",
        start: 29535447,
        end: 29546481
      }, {
        filename: "/lib/python3.15/test/test_capi/test_opt.py",
        start: 29546481,
        end: 29653754
      }, {
        filename: "/lib/python3.15/test/test_capi/test_pyatomic.py",
        start: 29653754,
        end: 29654158
      }, {
        filename: "/lib/python3.15/test/test_capi/test_run.py",
        start: 29654158,
        end: 29658789
      }, {
        filename: "/lib/python3.15/test/test_capi/test_set.py",
        start: 29658789,
        end: 29669878
      }, {
        filename: "/lib/python3.15/test/test_capi/test_structmembers.py",
        start: 29669878,
        end: 29676724
      }, {
        filename: "/lib/python3.15/test/test_capi/test_sys.py",
        start: 29676724,
        end: 29685329
      }, {
        filename: "/lib/python3.15/test/test_capi/test_time.py",
        start: 29685329,
        end: 29687745
      }, {
        filename: "/lib/python3.15/test/test_capi/test_tuple.py",
        start: 29687745,
        end: 29698652
      }, {
        filename: "/lib/python3.15/test/test_capi/test_type.py",
        start: 29698652,
        end: 29709166
      }, {
        filename: "/lib/python3.15/test/test_capi/test_unicode.py",
        start: 29709166,
        end: 29799713
      }, {
        filename: "/lib/python3.15/test/test_capi/test_watchers.py",
        start: 29799713,
        end: 29824309
      }, {
        filename: "/lib/python3.15/test/test_cext/__init__.py",
        start: 29824309,
        end: 29829488
      }, {
        filename: "/lib/python3.15/test/test_cext/extension.c",
        start: 29829488,
        end: 29832704
      }, {
        filename: "/lib/python3.15/test/test_cext/setup.py",
        start: 29832704,
        end: 29836895
      }, {
        filename: "/lib/python3.15/test/test_charmapcodec.py",
        start: 29836895,
        end: 29838709
      }, {
        filename: "/lib/python3.15/test/test_class.py",
        start: 29838709,
        end: 29868575
      }, {
        filename: "/lib/python3.15/test/test_clinic.py",
        start: 29868575,
        end: 30031390
      }, {
        filename: "/lib/python3.15/test/test_cmath.py",
        start: 30031390,
        end: 30054399
      }, {
        filename: "/lib/python3.15/test/test_cmd.py",
        start: 30054399,
        end: 30063470
      }, {
        filename: "/lib/python3.15/test/test_cmd_line.py",
        start: 30063470,
        end: 30119138
      }, {
        filename: "/lib/python3.15/test/test_cmd_line_script.py",
        start: 30119138,
        end: 30157133
      }, {
        filename: "/lib/python3.15/test/test_code.py",
        start: 30157133,
        end: 30208134
      }, {
        filename: "/lib/python3.15/test/test_code_module.py",
        start: 30208134,
        end: 30222816
      }, {
        filename: "/lib/python3.15/test/test_codeccallbacks.py",
        start: 30222816,
        end: 30274573
      }, {
        filename: "/lib/python3.15/test/test_codecencodings_cn.py",
        start: 30274573,
        end: 30278523
      }, {
        filename: "/lib/python3.15/test/test_codecencodings_hk.py",
        start: 30278523,
        end: 30279224
      }, {
        filename: "/lib/python3.15/test/test_codecencodings_iso2022.py",
        start: 30279224,
        end: 30282966
      }, {
        filename: "/lib/python3.15/test/test_codecencodings_jp.py",
        start: 30282966,
        end: 30287873
      }, {
        filename: "/lib/python3.15/test/test_codecencodings_kr.py",
        start: 30287873,
        end: 30290901
      }, {
        filename: "/lib/python3.15/test/test_codecencodings_tw.py",
        start: 30290901,
        end: 30291582
      }, {
        filename: "/lib/python3.15/test/test_codecmaps_cn.py",
        start: 30291582,
        end: 30292328
      }, {
        filename: "/lib/python3.15/test/test_codecmaps_hk.py",
        start: 30292328,
        end: 30292714
      }, {
        filename: "/lib/python3.15/test/test_codecmaps_jp.py",
        start: 30292714,
        end: 30294458
      }, {
        filename: "/lib/python3.15/test/test_codecmaps_kr.py",
        start: 30294458,
        end: 30295646
      }, {
        filename: "/lib/python3.15/test/test_codecmaps_tw.py",
        start: 30295646,
        end: 30296351
      }, {
        filename: "/lib/python3.15/test/test_codecs.py",
        start: 30296351,
        end: 30451256
      }, {
        filename: "/lib/python3.15/test/test_codeop.py",
        start: 30451256,
        end: 30460155
      }, {
        filename: "/lib/python3.15/test/test_collections.py",
        start: 30460155,
        end: 30556972
      }, {
        filename: "/lib/python3.15/test/test_colorsys.py",
        start: 30556972,
        end: 30561342
      }, {
        filename: "/lib/python3.15/test/test_compare.py",
        start: 30561342,
        end: 30579220
      }, {
        filename: "/lib/python3.15/test/test_compile.py",
        start: 30579220,
        end: 30687046
      }, {
        filename: "/lib/python3.15/test/test_compileall.py",
        start: 30687046,
        end: 30737770
      }, {
        filename: "/lib/python3.15/test/test_compiler_assemble.py",
        start: 30737770,
        end: 30742738
      }, {
        filename: "/lib/python3.15/test/test_compiler_codegen.py",
        start: 30742738,
        end: 30748304
      }, {
        filename: "/lib/python3.15/test/test_complex.py",
        start: 30748304,
        end: 30793708
      }, {
        filename: "/lib/python3.15/test/test_concurrent_futures/__init__.py",
        start: 30793708,
        end: 30794291
      }, {
        filename: "/lib/python3.15/test/test_concurrent_futures/executor.py",
        start: 30794291,
        end: 30803885
      }, {
        filename: "/lib/python3.15/test/test_concurrent_futures/test_as_completed.py",
        start: 30803885,
        end: 30808116
      }, {
        filename: "/lib/python3.15/test/test_concurrent_futures/test_deadlock.py",
        start: 30808116,
        end: 30821040
      }, {
        filename: "/lib/python3.15/test/test_concurrent_futures/test_future.py",
        start: 30821040,
        end: 30833229
      }, {
        filename: "/lib/python3.15/test/test_concurrent_futures/test_init.py",
        start: 30833229,
        end: 30838383
      }, {
        filename: "/lib/python3.15/test/test_concurrent_futures/test_interpreter_pool.py",
        start: 30838383,
        end: 30858311
      }, {
        filename: "/lib/python3.15/test/test_concurrent_futures/test_process_pool.py",
        start: 30858311,
        end: 30873414
      }, {
        filename: "/lib/python3.15/test/test_concurrent_futures/test_shutdown.py",
        start: 30873414,
        end: 30889722
      }, {
        filename: "/lib/python3.15/test/test_concurrent_futures/test_thread_pool.py",
        start: 30889722,
        end: 30894335
      }, {
        filename: "/lib/python3.15/test/test_concurrent_futures/test_wait.py",
        start: 30894335,
        end: 30901750
      }, {
        filename: "/lib/python3.15/test/test_concurrent_futures/util.py",
        start: 30901750,
        end: 30907347
      }, {
        filename: "/lib/python3.15/test/test_configparser.py",
        start: 30907347,
        end: 30999040
      }, {
        filename: "/lib/python3.15/test/test_contains.py",
        start: 30999040,
        end: 31002585
      }, {
        filename: "/lib/python3.15/test/test_context.py",
        start: 31002585,
        end: 31040076
      }, {
        filename: "/lib/python3.15/test/test_contextlib.py",
        start: 31040076,
        end: 31084449
      }, {
        filename: "/lib/python3.15/test/test_contextlib_async.py",
        start: 31084449,
        end: 31108494
      }, {
        filename: "/lib/python3.15/test/test_copy.py",
        start: 31108494,
        end: 31138901
      }, {
        filename: "/lib/python3.15/test/test_copyreg.py",
        start: 31138901,
        end: 31143369
      }, {
        filename: "/lib/python3.15/test/test_coroutines.py",
        start: 31143369,
        end: 31213222
      }, {
        filename: "/lib/python3.15/test/test_cppext/__init__.py",
        start: 31213222,
        end: 31217931
      }, {
        filename: "/lib/python3.15/test/test_cppext/extension.cpp",
        start: 31217931,
        end: 31226032
      }, {
        filename: "/lib/python3.15/test/test_cppext/setup.py",
        start: 31226032,
        end: 31230011
      }, {
        filename: "/lib/python3.15/test/test_crossinterp.py",
        start: 31230011,
        end: 31275511
      }, {
        filename: "/lib/python3.15/test/test_csv.py",
        start: 31275511,
        end: 31345539
      }, {
        filename: "/lib/python3.15/test/test_ctypes/__init__.py",
        start: 31345539,
        end: 31346325
      }, {
        filename: "/lib/python3.15/test/test_ctypes/__main__.py",
        start: 31346325,
        end: 31346398
      }, {
        filename: "/lib/python3.15/test/test_ctypes/_support.py",
        start: 31346398,
        end: 31352274
      }, {
        filename: "/lib/python3.15/test/test_ctypes/test_aligned_structures.py",
        start: 31352274,
        end: 31364382
      }, {
        filename: "/lib/python3.15/test/test_ctypes/test_anon.py",
        start: 31364382,
        end: 31367167
      }, {
        filename: "/lib/python3.15/test/test_ctypes/test_array_in_pointer.py",
        start: 31367167,
        end: 31368936
      }, {
        filename: "/lib/python3.15/test/test_ctypes/test_arrays.py",
        start: 31368936,
        end: 31378573
      }, {
        filename: "/lib/python3.15/test/test_ctypes/test_as_parameter.py",
        start: 31378573,
        end: 31386039
      }, {
        filename: "/lib/python3.15/test/test_ctypes/test_bitfields.py",
        start: 31386039,
        end: 31405957
      }, {
        filename: "/lib/python3.15/test/test_ctypes/test_buffers.py",
        start: 31405957,
        end: 31408537
      }, {
        filename: "/lib/python3.15/test/test_ctypes/test_bytes.py",
        start: 31408537,
        end: 31410678
      }, {
        filename: "/lib/python3.15/test/test_ctypes/test_byteswap.py",
        start: 31410678,
        end: 31424986
      }, {
        filename: "/lib/python3.15/test/test_ctypes/test_c_simple_type_meta.py",
        start: 31424986,
        end: 31438550
      }, {
        filename: "/lib/python3.15/test/test_ctypes/test_callbacks.py",
        start: 31438550,
        end: 31450070
      }, {
        filename: "/lib/python3.15/test/test_ctypes/test_cast.py",
        start: 31450070,
        end: 31453877
      }, {
        filename: "/lib/python3.15/test/test_ctypes/test_cfuncs.py",
        start: 31453877,
        end: 31462359
      }, {
        filename: "/lib/python3.15/test/test_ctypes/test_checkretval.py",
        start: 31462359,
        end: 31463439
      }, {
        filename: "/lib/python3.15/test/test_ctypes/test_delattr.py",
        start: 31463439,
        end: 31464001
      }, {
        filename: "/lib/python3.15/test/test_ctypes/test_dlerror.py",
        start: 31464001,
        end: 31470615
      }, {
        filename: "/lib/python3.15/test/test_ctypes/test_dllist.py",
        start: 31470615,
        end: 31472401
      }, {
        filename: "/lib/python3.15/test/test_ctypes/test_errno.py",
        start: 31472401,
        end: 31474706
      }, {
        filename: "/lib/python3.15/test/test_ctypes/test_find.py",
        start: 31474706,
        end: 31482843
      }, {
        filename: "/lib/python3.15/test/test_ctypes/test_frombuffer.py",
        start: 31482843,
        end: 31488121
      }, {
        filename: "/lib/python3.15/test/test_ctypes/test_funcptr.py",
        start: 31488121,
        end: 31492610
      }, {
        filename: "/lib/python3.15/test/test_ctypes/test_functions.py",
        start: 31492610,
        end: 31508140
      }, {
        filename: "/lib/python3.15/test/test_ctypes/test_generated_structs.py",
        start: 31508140,
        end: 31532425
      }, {
        filename: "/lib/python3.15/test/test_ctypes/test_incomplete.py",
        start: 31532425,
        end: 31534085
      }, {
        filename: "/lib/python3.15/test/test_ctypes/test_init.py",
        start: 31534085,
        end: 31535142
      }, {
        filename: "/lib/python3.15/test/test_ctypes/test_internals.py",
        start: 31535142,
        end: 31537685
      }, {
        filename: "/lib/python3.15/test/test_ctypes/test_keeprefs.py",
        start: 31537685,
        end: 31540707
      }, {
        filename: "/lib/python3.15/test/test_ctypes/test_libc.py",
        start: 31540707,
        end: 31543250
      }, {
        filename: "/lib/python3.15/test/test_ctypes/test_loading.py",
        start: 31543250,
        end: 31551290
      }, {
        filename: "/lib/python3.15/test/test_ctypes/test_macholib.py",
        start: 31551290,
        end: 31556230
      }, {
        filename: "/lib/python3.15/test/test_ctypes/test_memfunctions.py",
        start: 31556230,
        end: 31561553
      }, {
        filename: "/lib/python3.15/test/test_ctypes/test_numbers.py",
        start: 31561553,
        end: 31570055
      }, {
        filename: "/lib/python3.15/test/test_ctypes/test_objects.py",
        start: 31570055,
        end: 31571614
      }, {
        filename: "/lib/python3.15/test/test_ctypes/test_parameters.py",
        start: 31571614,
        end: 31583206
      }, {
        filename: "/lib/python3.15/test/test_ctypes/test_pep3118.py",
        start: 31583206,
        end: 31592428
      }, {
        filename: "/lib/python3.15/test/test_ctypes/test_pickling.py",
        start: 31592428,
        end: 31594924
      }, {
        filename: "/lib/python3.15/test/test_ctypes/test_pointers.py",
        start: 31594924,
        end: 31610351
      }, {
        filename: "/lib/python3.15/test/test_ctypes/test_prototypes.py",
        start: 31610351,
        end: 31618617
      }, {
        filename: "/lib/python3.15/test/test_ctypes/test_python_api.py",
        start: 31618617,
        end: 31621420
      }, {
        filename: "/lib/python3.15/test/test_ctypes/test_random_things.py",
        start: 31621420,
        end: 31624306
      }, {
        filename: "/lib/python3.15/test/test_ctypes/test_refcounts.py",
        start: 31624306,
        end: 31628702
      }, {
        filename: "/lib/python3.15/test/test_ctypes/test_repr.py",
        start: 31628702,
        end: 31629723
      }, {
        filename: "/lib/python3.15/test/test_ctypes/test_returnfuncptrs.py",
        start: 31629723,
        end: 31632751
      }, {
        filename: "/lib/python3.15/test/test_ctypes/test_simplesubclasses.py",
        start: 31632751,
        end: 31635888
      }, {
        filename: "/lib/python3.15/test/test_ctypes/test_sizes.py",
        start: 31635888,
        end: 31636974
      }, {
        filename: "/lib/python3.15/test/test_ctypes/test_slicing.py",
        start: 31636974,
        end: 31642707
      }, {
        filename: "/lib/python3.15/test/test_ctypes/test_stringptr.py",
        start: 31642707,
        end: 31645605
      }, {
        filename: "/lib/python3.15/test/test_ctypes/test_strings.py",
        start: 31645605,
        end: 31649456
      }, {
        filename: "/lib/python3.15/test/test_ctypes/test_struct_fields.py",
        start: 31649456,
        end: 31654772
      }, {
        filename: "/lib/python3.15/test/test_ctypes/test_structunion.py",
        start: 31654772,
        end: 31671138
      }, {
        filename: "/lib/python3.15/test/test_ctypes/test_structures.py",
        start: 31671138,
        end: 31695502
      }, {
        filename: "/lib/python3.15/test/test_ctypes/test_unaligned_structures.py",
        start: 31695502,
        end: 31696909
      }, {
        filename: "/lib/python3.15/test/test_ctypes/test_unicode.py",
        start: 31696909,
        end: 31698924
      }, {
        filename: "/lib/python3.15/test/test_ctypes/test_values.py",
        start: 31698924,
        end: 31703156
      }, {
        filename: "/lib/python3.15/test/test_ctypes/test_varsize_struct.py",
        start: 31703156,
        end: 31705031
      }, {
        filename: "/lib/python3.15/test/test_ctypes/test_win32.py",
        start: 31705031,
        end: 31710873
      }, {
        filename: "/lib/python3.15/test/test_ctypes/test_win32_com_foreign_func.py",
        start: 31710873,
        end: 31720041
      }, {
        filename: "/lib/python3.15/test/test_ctypes/test_wintypes.py",
        start: 31720041,
        end: 31722150
      }, {
        filename: "/lib/python3.15/test/test_curses.py",
        start: 31722150,
        end: 31774309
      }, {
        filename: "/lib/python3.15/test/test_dataclasses/__init__.py",
        start: 31774309,
        end: 31945983
      }, {
        filename: "/lib/python3.15/test/test_dataclasses/dataclass_module_1.py",
        start: 31945983,
        end: 31946820
      }, {
        filename: "/lib/python3.15/test/test_dataclasses/dataclass_module_1_str.py",
        start: 31946820,
        end: 31947655
      }, {
        filename: "/lib/python3.15/test/test_dataclasses/dataclass_module_2.py",
        start: 31947655,
        end: 31948411
      }, {
        filename: "/lib/python3.15/test/test_dataclasses/dataclass_module_2_str.py",
        start: 31948411,
        end: 31949165
      }, {
        filename: "/lib/python3.15/test/test_dataclasses/dataclass_textanno.py",
        start: 31949165,
        end: 31949291
      }, {
        filename: "/lib/python3.15/test/test_datetime.py",
        start: 31949291,
        end: 31952026
      }, {
        filename: "/lib/python3.15/test/test_dbm.py",
        start: 31952026,
        end: 31963022
      }, {
        filename: "/lib/python3.15/test/test_dbm_dumb.py",
        start: 31963022,
        end: 31977659
      }, {
        filename: "/lib/python3.15/test/test_dbm_gnu.py",
        start: 31977659,
        end: 31985880
      }, {
        filename: "/lib/python3.15/test/test_dbm_ndbm.py",
        start: 31985880,
        end: 31992333
      }, {
        filename: "/lib/python3.15/test/test_dbm_sqlite3.py",
        start: 31992333,
        end: 32003388
      }, {
        filename: "/lib/python3.15/test/test_decimal.py",
        start: 32003388,
        end: 32227657
      }, {
        filename: "/lib/python3.15/test/test_decorators.py",
        start: 32227657,
        end: 32238614
      }, {
        filename: "/lib/python3.15/test/test_defaultdict.py",
        start: 32238614,
        end: 32245331
      }, {
        filename: "/lib/python3.15/test/test_deque.py",
        start: 32245331,
        end: 32279286
      }, {
        filename: "/lib/python3.15/test/test_descr.py",
        start: 32279286,
        end: 32496386
      }, {
        filename: "/lib/python3.15/test/test_descrtut.py",
        start: 32496386,
        end: 32507689
      }, {
        filename: "/lib/python3.15/test/test_devpoll.py",
        start: 32507689,
        end: 32512238
      }, {
        filename: "/lib/python3.15/test/test_dict.py",
        start: 32512238,
        end: 32566024
      }, {
        filename: "/lib/python3.15/test/test_dictcomps.py",
        start: 32566024,
        end: 32572722
      }, {
        filename: "/lib/python3.15/test/test_dictviews.py",
        start: 32572722,
        end: 32588021
      }, {
        filename: "/lib/python3.15/test/test_difflib.py",
        start: 32588021,
        end: 32613821
      }, {
        filename: "/lib/python3.15/test/test_difflib_expect.html",
        start: 32613821,
        end: 32724012
      }, {
        filename: "/lib/python3.15/test/test_dis.py",
        start: 32724012,
        end: 32834282
      }, {
        filename: "/lib/python3.15/test/test_doctest/__init__.py",
        start: 32834282,
        end: 32834424
      }, {
        filename: "/lib/python3.15/test/test_doctest/decorator_mod.py",
        start: 32834424,
        end: 32834585
      }, {
        filename: "/lib/python3.15/test/test_doctest/doctest_aliases.py",
        start: 32834585,
        end: 32834825
      }, {
        filename: "/lib/python3.15/test/test_doctest/doctest_lineno.py",
        start: 32834825,
        end: 32836859
      }, {
        filename: "/lib/python3.15/test/test_doctest/sample_doctest.py",
        start: 32836859,
        end: 32837926
      }, {
        filename: "/lib/python3.15/test/test_doctest/sample_doctest_errors.py",
        start: 32837926,
        end: 32838471
      }, {
        filename: "/lib/python3.15/test/test_doctest/sample_doctest_no_docstrings.py",
        start: 32838471,
        end: 32838698
      }, {
        filename: "/lib/python3.15/test/test_doctest/sample_doctest_no_doctests.py",
        start: 32838698,
        end: 32838967
      }, {
        filename: "/lib/python3.15/test/test_doctest/sample_doctest_skip.py",
        start: 32838967,
        end: 32839681
      }, {
        filename: "/lib/python3.15/test/test_doctest/test_doctest.py",
        start: 32839681,
        end: 32969590
      }, {
        filename: "/lib/python3.15/test/test_doctest/test_doctest.txt",
        start: 32969590,
        end: 32969890
      }, {
        filename: "/lib/python3.15/test/test_doctest/test_doctest2.py",
        start: 32969890,
        end: 32972305
      }, {
        filename: "/lib/python3.15/test/test_doctest/test_doctest2.txt",
        start: 32972305,
        end: 32972723
      }, {
        filename: "/lib/python3.15/test/test_doctest/test_doctest3.txt",
        start: 32972723,
        end: 32972805
      }, {
        filename: "/lib/python3.15/test/test_doctest/test_doctest4.txt",
        start: 32972805,
        end: 32973049
      }, {
        filename: "/lib/python3.15/test/test_doctest/test_doctest_errors.txt",
        start: 32973049,
        end: 32973239
      }, {
        filename: "/lib/python3.15/test/test_doctest/test_doctest_skip.txt",
        start: 32973239,
        end: 32973384
      }, {
        filename: "/lib/python3.15/test/test_doctest/test_doctest_skip2.txt",
        start: 32973384,
        end: 32973512
      }, {
        filename: "/lib/python3.15/test/test_docxmlrpc.py",
        start: 32973512,
        end: 32982829
      }, {
        filename: "/lib/python3.15/test/test_dtrace.py",
        start: 32982829,
        end: 32990999
      }, {
        filename: "/lib/python3.15/test/test_dynamic.py",
        start: 32990999,
        end: 32997197
      }, {
        filename: "/lib/python3.15/test/test_dynamicclassattribute.py",
        start: 32997197,
        end: 33006978
      }, {
        filename: "/lib/python3.15/test/test_eintr.py",
        start: 33006978,
        end: 33007605
      }, {
        filename: "/lib/python3.15/test/test_email/__init__.py",
        start: 33007605,
        end: 33013946
      }, {
        filename: "/lib/python3.15/test/test_email/__main__.py",
        start: 33013946,
        end: 33014018
      }, {
        filename: "/lib/python3.15/test/test_email/data/msg_01.txt",
        start: 33014018,
        end: 33014477
      }, {
        filename: "/lib/python3.15/test/test_email/data/msg_02.txt",
        start: 33014477,
        end: 33017289
      }, {
        filename: "/lib/python3.15/test/test_email/data/msg_03.txt",
        start: 33017289,
        end: 33017655
      }, {
        filename: "/lib/python3.15/test/test_email/data/msg_04.txt",
        start: 33017655,
        end: 33018616
      }, {
        filename: "/lib/python3.15/test/test_email/data/msg_05.txt",
        start: 33018616,
        end: 33019174
      }, {
        filename: "/lib/python3.15/test/test_email/data/msg_06.txt",
        start: 33019174,
        end: 33020215
      }, {
        filename: "/lib/python3.15/test/test_email/data/msg_07.txt",
        start: 33020215,
        end: 33025442
      }, {
        filename: "/lib/python3.15/test/test_email/data/msg_08.txt",
        start: 33025442,
        end: 33025896
      }, {
        filename: "/lib/python3.15/test/test_email/data/msg_09.txt",
        start: 33025896,
        end: 33026328
      }, {
        filename: "/lib/python3.15/test/test_email/data/msg_10.txt",
        start: 33026328,
        end: 33027212
      }, {
        filename: "/lib/python3.15/test/test_email/data/msg_11.txt",
        start: 33027212,
        end: 33027354
      }, {
        filename: "/lib/python3.15/test/test_email/data/msg_12.txt",
        start: 33027354,
        end: 33027998
      }, {
        filename: "/lib/python3.15/test/test_email/data/msg_12a.txt",
        start: 33027998,
        end: 33028644
      }, {
        filename: "/lib/python3.15/test/test_email/data/msg_13.txt",
        start: 33028644,
        end: 33034011
      }, {
        filename: "/lib/python3.15/test/test_email/data/msg_14.txt",
        start: 33034011,
        end: 33034652
      }, {
        filename: "/lib/python3.15/test/test_email/data/msg_15.txt",
        start: 33034652,
        end: 33035958
      }, {
        filename: "/lib/python3.15/test/test_email/data/msg_16.txt",
        start: 33035958,
        end: 33041161
      }, {
        filename: "/lib/python3.15/test/test_email/data/msg_17.txt",
        start: 33041161,
        end: 33041491
      }, {
        filename: "/lib/python3.15/test/test_email/data/msg_18.txt",
        start: 33041491,
        end: 33041721
      }, {
        filename: "/lib/python3.15/test/test_email/data/msg_19.txt",
        start: 33041721,
        end: 33042478
      }, {
        filename: "/lib/python3.15/test/test_email/data/msg_20.txt",
        start: 33042478,
        end: 33042985
      }, {
        filename: "/lib/python3.15/test/test_email/data/msg_21.txt",
        start: 33042985,
        end: 33043361
      }, {
        filename: "/lib/python3.15/test/test_email/data/msg_22.txt",
        start: 33043361,
        end: 33045255
      }, {
        filename: "/lib/python3.15/test/test_email/data/msg_23.txt",
        start: 33045255,
        end: 33045394
      }, {
        filename: "/lib/python3.15/test/test_email/data/msg_24.txt",
        start: 33045394,
        end: 33045551
      }, {
        filename: "/lib/python3.15/test/test_email/data/msg_25.txt",
        start: 33045551,
        end: 33050673
      }, {
        filename: "/lib/python3.15/test/test_email/data/msg_26.txt",
        start: 33050673,
        end: 33052776
      }, {
        filename: "/lib/python3.15/test/test_email/data/msg_27.txt",
        start: 33052776,
        end: 33053354
      }, {
        filename: "/lib/python3.15/test/test_email/data/msg_28.txt",
        start: 33053354,
        end: 33053734
      }, {
        filename: "/lib/python3.15/test/test_email/data/msg_29.txt",
        start: 33053734,
        end: 33054317
      }, {
        filename: "/lib/python3.15/test/test_email/data/msg_30.txt",
        start: 33054317,
        end: 33054639
      }, {
        filename: "/lib/python3.15/test/test_email/data/msg_31.txt",
        start: 33054639,
        end: 33054839
      }, {
        filename: "/lib/python3.15/test/test_email/data/msg_32.txt",
        start: 33054839,
        end: 33055257
      }, {
        filename: "/lib/python3.15/test/test_email/data/msg_33.txt",
        start: 33055257,
        end: 33056007
      }, {
        filename: "/lib/python3.15/test/test_email/data/msg_34.txt",
        start: 33056007,
        end: 33056307
      }, {
        filename: "/lib/python3.15/test/test_email/data/msg_35.txt",
        start: 33056307,
        end: 33056443
      }, {
        filename: "/lib/python3.15/test/test_email/data/msg_36.txt",
        start: 33056443,
        end: 33057259
      }, {
        filename: "/lib/python3.15/test/test_email/data/msg_37.txt",
        start: 33057259,
        end: 33057468
      }, {
        filename: "/lib/python3.15/test/test_email/data/msg_38.txt",
        start: 33057468,
        end: 33060016
      }, {
        filename: "/lib/python3.15/test/test_email/data/msg_39.txt",
        start: 33060016,
        end: 33061971
      }, {
        filename: "/lib/python3.15/test/test_email/data/msg_40.txt",
        start: 33061971,
        end: 33062168
      }, {
        filename: "/lib/python3.15/test/test_email/data/msg_41.txt",
        start: 33062168,
        end: 33062353
      }, {
        filename: "/lib/python3.15/test/test_email/data/msg_42.txt",
        start: 33062353,
        end: 33062666
      }, {
        filename: "/lib/python3.15/test/test_email/data/msg_43.txt",
        start: 33062666,
        end: 33071832
      }, {
        filename: "/lib/python3.15/test/test_email/data/msg_44.txt",
        start: 33071832,
        end: 33072727
      }, {
        filename: "/lib/python3.15/test/test_email/data/msg_45.txt",
        start: 33072727,
        end: 33073692
      }, {
        filename: "/lib/python3.15/test/test_email/data/msg_46.txt",
        start: 33073692,
        end: 33074508
      }, {
        filename: "/lib/python3.15/test/test_email/data/msg_47.txt",
        start: 33074508,
        end: 33074740
      }, {
        filename: "/lib/python3.15/test/test_email/data/python.bmp",
        start: 33074740,
        end: 33075902
      }, {
        filename: "/lib/python3.15/test/test_email/data/python.exr",
        start: 33075902,
        end: 33078537
      }, {
        filename: "/lib/python3.15/test/test_email/data/python.gif",
        start: 33078537,
        end: 33078942
      }, {
        filename: "/lib/python3.15/test/test_email/data/python.jpg",
        start: 33078942,
        end: 33079485
      }, {
        filename: "/lib/python3.15/test/test_email/data/python.pbm",
        start: 33079485,
        end: 33079526
      }, {
        filename: "/lib/python3.15/test/test_email/data/python.pgm",
        start: 33079526,
        end: 33079795
      }, {
        filename: "/lib/python3.15/test/test_email/data/python.png",
        start: 33079795,
        end: 33080815
      }, {
        filename: "/lib/python3.15/test/test_email/data/python.ppm",
        start: 33080815,
        end: 33081596
      }, {
        filename: "/lib/python3.15/test/test_email/data/python.ras",
        start: 33081596,
        end: 33082652
      }, {
        filename: "/lib/python3.15/test/test_email/data/python.sgi",
        start: 33082652,
        end: 33084619
      }, {
        filename: "/lib/python3.15/test/test_email/data/python.tiff",
        start: 33084619,
        end: 33085945
      }, {
        filename: "/lib/python3.15/test/test_email/data/python.webp",
        start: 33085945,
        end: 33086377
      }, {
        filename: "/lib/python3.15/test/test_email/data/python.xbm",
        start: 33086377,
        end: 33086659
      }, {
        filename: "/lib/python3.15/test/test_email/data/sndhdr.aifc",
        start: 33086659,
        end: 33086765
      }, {
        filename: "/lib/python3.15/test/test_email/data/sndhdr.aiff",
        start: 33086765,
        end: 33086873
      }, {
        filename: "/lib/python3.15/test/test_email/data/sndhdr.au",
        start: 33086873,
        end: 33115017
      }, {
        filename: "/lib/python3.15/test/test_email/data/sndhdr.wav",
        start: 33115017,
        end: 33115081,
        audio: 1
      }, {
        filename: "/lib/python3.15/test/test_email/test__encoded_words.py",
        start: 33115081,
        end: 33122166
      }, {
        filename: "/lib/python3.15/test/test_email/test__header_value_parser.py",
        start: 33122166,
        end: 33264132
      }, {
        filename: "/lib/python3.15/test/test_email/test_asian_codecs.py",
        start: 33264132,
        end: 33267272
      }, {
        filename: "/lib/python3.15/test/test_email/test_contentmanager.py",
        start: 33267272,
        end: 33302372
      }, {
        filename: "/lib/python3.15/test/test_email/test_defect_handling.py",
        start: 33302372,
        end: 33315702
      }, {
        filename: "/lib/python3.15/test/test_email/test_email.py",
        start: 33315702,
        end: 33542712
      }, {
        filename: "/lib/python3.15/test/test_email/test_generator.py",
        start: 33542712,
        end: 33561241
      }, {
        filename: "/lib/python3.15/test/test_email/test_headerregistry.py",
        start: 33561241,
        end: 33628134
      }, {
        filename: "/lib/python3.15/test/test_email/test_inversion.py",
        start: 33628134,
        end: 33630427
      }, {
        filename: "/lib/python3.15/test/test_email/test_message.py",
        start: 33630427,
        end: 33671056
      }, {
        filename: "/lib/python3.15/test/test_email/test_parser.py",
        start: 33671056,
        end: 33675389
      }, {
        filename: "/lib/python3.15/test/test_email/test_pickleable.py",
        start: 33675389,
        end: 33677938
      }, {
        filename: "/lib/python3.15/test/test_email/test_policy.py",
        start: 33677938,
        end: 33695360
      }, {
        filename: "/lib/python3.15/test/test_email/test_utils.py",
        start: 33695360,
        end: 33702751
      }, {
        filename: "/lib/python3.15/test/test_email/torture_test.py",
        start: 33702751,
        end: 33706278
      }, {
        filename: "/lib/python3.15/test/test_embed.py",
        start: 33706278,
        end: 33784681
      }, {
        filename: "/lib/python3.15/test/test_ensurepip.py",
        start: 33784681,
        end: 33797050
      }, {
        filename: "/lib/python3.15/test/test_enum.py",
        start: 33797050,
        end: 33998970
      }, {
        filename: "/lib/python3.15/test/test_enumerate.py",
        start: 33998970,
        end: 34008326
      }, {
        filename: "/lib/python3.15/test/test_eof.py",
        start: 34008326,
        end: 34016527
      }, {
        filename: "/lib/python3.15/test/test_epoll.py",
        start: 34016527,
        end: 34026157
      }, {
        filename: "/lib/python3.15/test/test_errno.py",
        start: 34026157,
        end: 34027091
      }, {
        filename: "/lib/python3.15/test/test_except_star.py",
        start: 34027091,
        end: 34067788
      }, {
        filename: "/lib/python3.15/test/test_exception_group.py",
        start: 34067788,
        end: 34105913
      }, {
        filename: "/lib/python3.15/test/test_exception_hierarchy.py",
        start: 34105913,
        end: 34113634
      }, {
        filename: "/lib/python3.15/test/test_exception_variations.py",
        start: 34113634,
        end: 34127702
      }, {
        filename: "/lib/python3.15/test/test_exceptions.py",
        start: 34127702,
        end: 34221668
      }, {
        filename: "/lib/python3.15/test/test_extcall.py",
        start: 34221668,
        end: 34236447
      }, {
        filename: "/lib/python3.15/test/test_external_inspection.py",
        start: 34236447,
        end: 34365824
      }, {
        filename: "/lib/python3.15/test/test_faulthandler.py",
        start: 34365824,
        end: 34399771
      }, {
        filename: "/lib/python3.15/test/test_fcntl.py",
        start: 34399771,
        end: 34410753
      }, {
        filename: "/lib/python3.15/test/test_file_eintr.py",
        start: 34410753,
        end: 34421776
      }, {
        filename: "/lib/python3.15/test/test_filecmp.py",
        start: 34421776,
        end: 34437816
      }, {
        filename: "/lib/python3.15/test/test_fileinput.py",
        start: 34437816,
        end: 34476585
      }, {
        filename: "/lib/python3.15/test/test_fileutils.py",
        start: 34476585,
        end: 34477536
      }, {
        filename: "/lib/python3.15/test/test_finalization.py",
        start: 34477536,
        end: 34493239
      }, {
        filename: "/lib/python3.15/test/test_float.py",
        start: 34493239,
        end: 34563389
      }, {
        filename: "/lib/python3.15/test/test_flufl.py",
        start: 34563389,
        end: 34566263
      }, {
        filename: "/lib/python3.15/test/test_fnmatch.py",
        start: 34566263,
        end: 34580744
      }, {
        filename: "/lib/python3.15/test/test_fork1.py",
        start: 34580744,
        end: 34584300
      }, {
        filename: "/lib/python3.15/test/test_format.py",
        start: 34584300,
        end: 34614106
      }, {
        filename: "/lib/python3.15/test/test_fractions.py",
        start: 34614106,
        end: 34686858
      }, {
        filename: "/lib/python3.15/test/test_frame.py",
        start: 34686858,
        end: 34710538
      }, {
        filename: "/lib/python3.15/test/test_free_threading/__init__.py",
        start: 34710538,
        end: 34710763
      }, {
        filename: "/lib/python3.15/test/test_free_threading/test_bisect.py",
        start: 34710763,
        end: 34712478
      }, {
        filename: "/lib/python3.15/test/test_free_threading/test_bz2.py",
        start: 34712478,
        end: 34714689
      }, {
        filename: "/lib/python3.15/test/test_free_threading/test_capi.py",
        start: 34714689,
        end: 34716222
      }, {
        filename: "/lib/python3.15/test/test_free_threading/test_code.py",
        start: 34716222,
        end: 34717134
      }, {
        filename: "/lib/python3.15/test/test_free_threading/test_cprofile.py",
        start: 34717134,
        end: 34718646
      }, {
        filename: "/lib/python3.15/test/test_free_threading/test_csv.py",
        start: 34718646,
        end: 34720171
      }, {
        filename: "/lib/python3.15/test/test_free_threading/test_dbm_gnu.py",
        start: 34720171,
        end: 34722985
      }, {
        filename: "/lib/python3.15/test/test_free_threading/test_dict.py",
        start: 34722985,
        end: 34729866
      }, {
        filename: "/lib/python3.15/test/test_free_threading/test_enumerate.py",
        start: 34729866,
        end: 34730942
      }, {
        filename: "/lib/python3.15/test/test_free_threading/test_func_annotations.py",
        start: 34730942,
        end: 34733545
      }, {
        filename: "/lib/python3.15/test/test_free_threading/test_functools.py",
        start: 34733545,
        end: 34735534
      }, {
        filename: "/lib/python3.15/test/test_free_threading/test_gc.py",
        start: 34735534,
        end: 34737179
      }, {
        filename: "/lib/python3.15/test/test_free_threading/test_generators.py",
        start: 34737179,
        end: 34740800
      }, {
        filename: "/lib/python3.15/test/test_free_threading/test_grp.py",
        start: 34740800,
        end: 34741754
      }, {
        filename: "/lib/python3.15/test/test_free_threading/test_heapq.py",
        start: 34741754,
        end: 34749250
      }, {
        filename: "/lib/python3.15/test/test_free_threading/test_io.py",
        start: 34749250,
        end: 34753132
      }, {
        filename: "/lib/python3.15/test/test_free_threading/test_iteration.py",
        start: 34753132,
        end: 34757781
      }, {
        filename: "/lib/python3.15/test/test_free_threading/test_itertools.py",
        start: 34757781,
        end: 34760468
      }, {
        filename: "/lib/python3.15/test/test_free_threading/test_itertools_combinatoric.py",
        start: 34760468,
        end: 34761899
      }, {
        filename: "/lib/python3.15/test/test_free_threading/test_json.py",
        start: 34761899,
        end: 34764207
      }, {
        filename: "/lib/python3.15/test/test_free_threading/test_list.py",
        start: 34764207,
        end: 34766663
      }, {
        filename: "/lib/python3.15/test/test_free_threading/test_lzma.py",
        start: 34766663,
        end: 34768427
      }, {
        filename: "/lib/python3.15/test/test_free_threading/test_methodcaller.py",
        start: 34768427,
        end: 34769200
      }, {
        filename: "/lib/python3.15/test/test_free_threading/test_mmap.py",
        start: 34769200,
        end: 34780470
      }, {
        filename: "/lib/python3.15/test/test_free_threading/test_monitoring.py",
        start: 34780470,
        end: 34792903
      }, {
        filename: "/lib/python3.15/test/test_free_threading/test_pwd.py",
        start: 34792903,
        end: 34793787
      }, {
        filename: "/lib/python3.15/test/test_free_threading/test_races.py",
        start: 34793787,
        end: 34802158
      }, {
        filename: "/lib/python3.15/test/test_free_threading/test_re.py",
        start: 34802158,
        end: 34804245
      }, {
        filename: "/lib/python3.15/test/test_free_threading/test_resource.py",
        start: 34804245,
        end: 34805626
      }, {
        filename: "/lib/python3.15/test/test_free_threading/test_reversed.py",
        start: 34805626,
        end: 34806802
      }, {
        filename: "/lib/python3.15/test/test_free_threading/test_set.py",
        start: 34806802,
        end: 34811546
      }, {
        filename: "/lib/python3.15/test/test_free_threading/test_slots.py",
        start: 34811546,
        end: 34819510
      }, {
        filename: "/lib/python3.15/test/test_free_threading/test_str.py",
        start: 34819510,
        end: 34821513
      }, {
        filename: "/lib/python3.15/test/test_free_threading/test_suggestions.py",
        start: 34821513,
        end: 34822139
      }, {
        filename: "/lib/python3.15/test/test_free_threading/test_syslog.py",
        start: 34822139,
        end: 34823602
      }, {
        filename: "/lib/python3.15/test/test_free_threading/test_tokenize.py",
        start: 34823602,
        end: 34825815
      }, {
        filename: "/lib/python3.15/test/test_free_threading/test_type.py",
        start: 34825815,
        end: 34830140
      }, {
        filename: "/lib/python3.15/test/test_free_threading/test_uuid.py",
        start: 34830140,
        end: 34832102
      }, {
        filename: "/lib/python3.15/test/test_free_threading/test_zip.py",
        start: 34832102,
        end: 34833168
      }, {
        filename: "/lib/python3.15/test/test_free_threading/test_zlib.py",
        start: 34833168,
        end: 34835772
      }, {
        filename: "/lib/python3.15/test/test_frozen.py",
        start: 34835772,
        end: 34838023
      }, {
        filename: "/lib/python3.15/test/test_fstring.py",
        start: 34838023,
        end: 34910997
      }, {
        filename: "/lib/python3.15/test/test_ftplib.py",
        start: 34910997,
        end: 34954066
      }, {
        filename: "/lib/python3.15/test/test_funcattrs.py",
        start: 34954066,
        end: 34971770
      }, {
        filename: "/lib/python3.15/test/test_functools.py",
        start: 34971770,
        end: 35105923
      }, {
        filename: "/lib/python3.15/test/test_future_stmt/__init__.py",
        start: 35105923,
        end: 35106055
      }, {
        filename: "/lib/python3.15/test/test_future_stmt/badsyntax_future.py",
        start: 35106055,
        end: 35106150
      }, {
        filename: "/lib/python3.15/test/test_future_stmt/import_nested_scope_twice.py",
        start: 35106150,
        end: 35106379
      }, {
        filename: "/lib/python3.15/test/test_future_stmt/nested_scope.py",
        start: 35106379,
        end: 35106542
      }, {
        filename: "/lib/python3.15/test/test_future_stmt/test_future.py",
        start: 35106542,
        end: 35126005
      }, {
        filename: "/lib/python3.15/test/test_future_stmt/test_future_flags.py",
        start: 35126005,
        end: 35128426
      }, {
        filename: "/lib/python3.15/test/test_future_stmt/test_future_multiple_features.py",
        start: 35128426,
        end: 35128936
      }, {
        filename: "/lib/python3.15/test/test_future_stmt/test_future_multiple_imports.py",
        start: 35128936,
        end: 35129158
      }, {
        filename: "/lib/python3.15/test/test_future_stmt/test_future_single_import.py",
        start: 35129158,
        end: 35129648
      }, {
        filename: "/lib/python3.15/test/test_gc.py",
        start: 35129648,
        end: 35188013
      }, {
        filename: "/lib/python3.15/test/test_gdb/__init__.py",
        start: 35188013,
        end: 35189042
      }, {
        filename: "/lib/python3.15/test/test_gdb/gdb_sample.py",
        start: 35189042,
        end: 35189198
      }, {
        filename: "/lib/python3.15/test/test_gdb/test_backtrace.py",
        start: 35189198,
        end: 35194221
      }, {
        filename: "/lib/python3.15/test/test_gdb/test_cfunction.py",
        start: 35194221,
        end: 35197144
      }, {
        filename: "/lib/python3.15/test/test_gdb/test_cfunction_full.py",
        start: 35197144,
        end: 35198147
      }, {
        filename: "/lib/python3.15/test/test_gdb/test_misc.py",
        start: 35198147,
        end: 35205915
      }, {
        filename: "/lib/python3.15/test/test_gdb/test_pretty_print.py",
        start: 35205915,
        end: 35223691
      }, {
        filename: "/lib/python3.15/test/test_gdb/util.py",
        start: 35223691,
        end: 35234153
      }, {
        filename: "/lib/python3.15/test/test_generated_cases.py",
        start: 35234153,
        end: 35301534
      }, {
        filename: "/lib/python3.15/test/test_generator_stop.py",
        start: 35301534,
        end: 35302477
      }, {
        filename: "/lib/python3.15/test/test_generators.py",
        start: 35302477,
        end: 35380334
      }, {
        filename: "/lib/python3.15/test/test_genericalias.py",
        start: 35380334,
        end: 35402663
      }, {
        filename: "/lib/python3.15/test/test_genericclass.py",
        start: 35402663,
        end: 35412459
      }, {
        filename: "/lib/python3.15/test/test_genericpath.py",
        start: 35412459,
        end: 35437073
      }, {
        filename: "/lib/python3.15/test/test_genexps.py",
        start: 35437073,
        end: 35444274
      }, {
        filename: "/lib/python3.15/test/test_getopt.py",
        start: 35444274,
        end: 35453921
      }, {
        filename: "/lib/python3.15/test/test_getpass.py",
        start: 35453921,
        end: 35463617
      }, {
        filename: "/lib/python3.15/test/test_getpath.py",
        start: 35463617,
        end: 35511209
      }, {
        filename: "/lib/python3.15/test/test_gettext.py",
        start: 35511209,
        end: 35555977
      }, {
        filename: "/lib/python3.15/test/test_glob.py",
        start: 35555977,
        end: 35577534
      }, {
        filename: "/lib/python3.15/test/test_global.py",
        start: 35577534,
        end: 35584140
      }, {
        filename: "/lib/python3.15/test/test_grammar.py",
        start: 35584140,
        end: 35652551
      }, {
        filename: "/lib/python3.15/test/test_graphlib.py",
        start: 35652551,
        end: 35661519
      }, {
        filename: "/lib/python3.15/test/test_grp.py",
        start: 35661519,
        end: 35665277
      }, {
        filename: "/lib/python3.15/test/test_gzip.py",
        start: 35665277,
        end: 35710055
      }, {
        filename: "/lib/python3.15/test/test_hash.py",
        start: 35710055,
        end: 35722459
      }, {
        filename: "/lib/python3.15/test/test_hashlib.py",
        start: 35722459,
        end: 35780402
      }, {
        filename: "/lib/python3.15/test/test_heapq.py",
        start: 35780402,
        end: 35803788
      }, {
        filename: "/lib/python3.15/test/test_hmac.py",
        start: 35803788,
        end: 35863519
      }, {
        filename: "/lib/python3.15/test/test_html.py",
        start: 35863519,
        end: 35867855
      }, {
        filename: "/lib/python3.15/test/test_htmlparser.py",
        start: 35867855,
        end: 35920170
      }, {
        filename: "/lib/python3.15/test/test_http_cookiejar.py",
        start: 35920170,
        end: 36004274
      }, {
        filename: "/lib/python3.15/test/test_http_cookies.py",
        start: 36004274,
        end: 36028127
      }, {
        filename: "/lib/python3.15/test/test_httplib.py",
        start: 36028127,
        end: 36132339
      }, {
        filename: "/lib/python3.15/test/test_httpservers.py",
        start: 36132339,
        end: 36197145
      }, {
        filename: "/lib/python3.15/test/test_idle.py",
        start: 36197145,
        end: 36198021
      }, {
        filename: "/lib/python3.15/test/test_imaplib.py",
        start: 36198021,
        end: 36243286
      }, {
        filename: "/lib/python3.15/test/test_import/__init__.py",
        start: 36243286,
        end: 36377830
      }, {
        filename: "/lib/python3.15/test/test_import/__main__.py",
        start: 36377830,
        end: 36377881
      }, {
        filename: "/lib/python3.15/test/test_import/data/circular_imports/basic.py",
        start: 36377881,
        end: 36377959
      }, {
        filename: "/lib/python3.15/test/test_import/data/circular_imports/basic2.py",
        start: 36377959,
        end: 36377979
      }, {
        filename: "/lib/python3.15/test/test_import/data/circular_imports/binding.py",
        start: 36377979,
        end: 36378046
      }, {
        filename: "/lib/python3.15/test/test_import/data/circular_imports/binding2.py",
        start: 36378046,
        end: 36378111
      }, {
        filename: "/lib/python3.15/test/test_import/data/circular_imports/from_cycle1.py",
        start: 36378111,
        end: 36378144
      }, {
        filename: "/lib/python3.15/test/test_import/data/circular_imports/from_cycle2.py",
        start: 36378144,
        end: 36378177
      }, {
        filename: "/lib/python3.15/test/test_import/data/circular_imports/import_cycle.py",
        start: 36378177,
        end: 36378259
      }, {
        filename: "/lib/python3.15/test/test_import/data/circular_imports/indirect.py",
        start: 36378259,
        end: 36378287
      }, {
        filename: "/lib/python3.15/test/test_import/data/circular_imports/rebinding.py",
        start: 36378287,
        end: 36378409
      }, {
        filename: "/lib/python3.15/test/test_import/data/circular_imports/rebinding2.py",
        start: 36378409,
        end: 36378475
      }, {
        filename: "/lib/python3.15/test/test_import/data/circular_imports/singlephase.py",
        start: 36378475,
        end: 36378880
      }, {
        filename: "/lib/python3.15/test/test_import/data/circular_imports/source.py",
        start: 36378880,
        end: 36378907
      }, {
        filename: "/lib/python3.15/test/test_import/data/circular_imports/subpackage.py",
        start: 36378907,
        end: 36378986
      }, {
        filename: "/lib/python3.15/test/test_import/data/circular_imports/subpkg/subpackage2.py",
        start: 36378986,
        end: 36379036
      }, {
        filename: "/lib/python3.15/test/test_import/data/circular_imports/subpkg/util.py",
        start: 36379036,
        end: 36379057
      }, {
        filename: "/lib/python3.15/test/test_import/data/circular_imports/subpkg2/__init__.py",
        start: 36379057,
        end: 36379057
      }, {
        filename: "/lib/python3.15/test/test_import/data/circular_imports/subpkg2/parent/__init__.py",
        start: 36379057,
        end: 36379124
      }, {
        filename: "/lib/python3.15/test/test_import/data/circular_imports/subpkg2/parent/child.py",
        start: 36379124,
        end: 36379240
      }, {
        filename: "/lib/python3.15/test/test_import/data/circular_imports/use.py",
        start: 36379240,
        end: 36379273
      }, {
        filename: "/lib/python3.15/test/test_import/data/circular_imports/util.py",
        start: 36379273,
        end: 36379294
      }, {
        filename: "/lib/python3.15/test/test_import/data/double_const.py",
        start: 36379294,
        end: 36380506
      }, {
        filename: "/lib/python3.15/test/test_import/data/package/__init__.py",
        start: 36380506,
        end: 36380549
      }, {
        filename: "/lib/python3.15/test/test_import/data/package/submodule.py",
        start: 36380549,
        end: 36380549
      }, {
        filename: "/lib/python3.15/test/test_import/data/package2/submodule1.py",
        start: 36380549,
        end: 36380620
      }, {
        filename: "/lib/python3.15/test/test_import/data/package2/submodule2.py",
        start: 36380620,
        end: 36380620
      }, {
        filename: "/lib/python3.15/test/test_import/data/package3/__init__.py",
        start: 36380620,
        end: 36380719
      }, {
        filename: "/lib/python3.15/test/test_import/data/package3/submodule.py",
        start: 36380719,
        end: 36380846
      }, {
        filename: "/lib/python3.15/test/test_import/data/package4/__init__.py",
        start: 36380846,
        end: 36380986
      }, {
        filename: "/lib/python3.15/test/test_import/data/package4/submodule.py",
        start: 36380986,
        end: 36381037
      }, {
        filename: "/lib/python3.15/test/test_import/data/syntax_warnings.py",
        start: 36381037,
        end: 36381460
      }, {
        filename: "/lib/python3.15/test/test_import/data/unwritable/__init__.py",
        start: 36381460,
        end: 36381791
      }, {
        filename: "/lib/python3.15/test/test_import/data/unwritable/x.py",
        start: 36381791,
        end: 36381791
      }, {
        filename: "/lib/python3.15/test/test_importlib/__init__.py",
        start: 36381791,
        end: 36381933
      }, {
        filename: "/lib/python3.15/test/test_importlib/__main__.py",
        start: 36381933,
        end: 36381991
      }, {
        filename: "/lib/python3.15/test/test_importlib/abc.py",
        start: 36381991,
        end: 36383938
      }, {
        filename: "/lib/python3.15/test/test_importlib/builtin/__init__.py",
        start: 36383938,
        end: 36384080
      }, {
        filename: "/lib/python3.15/test/test_importlib/builtin/__main__.py",
        start: 36384080,
        end: 36384138
      }, {
        filename: "/lib/python3.15/test/test_importlib/builtin/test_finder.py",
        start: 36384138,
        end: 36385383
      }, {
        filename: "/lib/python3.15/test/test_importlib/builtin/test_loader.py",
        start: 36385383,
        end: 36386826
      }, {
        filename: "/lib/python3.15/test/test_importlib/extension/__init__.py",
        start: 36386826,
        end: 36386968
      }, {
        filename: "/lib/python3.15/test/test_importlib/extension/__main__.py",
        start: 36386968,
        end: 36387026
      }, {
        filename: "/lib/python3.15/test/test_importlib/extension/_test_nonmodule_cases.py",
        start: 36387026,
        end: 36388490
      }, {
        filename: "/lib/python3.15/test/test_importlib/extension/test_case_sensitivity.py",
        start: 36388490,
        end: 36390273
      }, {
        filename: "/lib/python3.15/test/test_importlib/extension/test_finder.py",
        start: 36390273,
        end: 36392327
      }, {
        filename: "/lib/python3.15/test/test_importlib/extension/test_loader.py",
        start: 36392327,
        end: 36402565
      }, {
        filename: "/lib/python3.15/test/test_importlib/extension/test_path_hook.py",
        start: 36402565,
        end: 36403595
      }, {
        filename: "/lib/python3.15/test/test_importlib/frozen/__init__.py",
        start: 36403595,
        end: 36403737
      }, {
        filename: "/lib/python3.15/test/test_importlib/frozen/__main__.py",
        start: 36403737,
        end: 36403795
      }, {
        filename: "/lib/python3.15/test/test_importlib/frozen/test_finder.py",
        start: 36403795,
        end: 36410310
      }, {
        filename: "/lib/python3.15/test/test_importlib/frozen/test_loader.py",
        start: 36410310,
        end: 36416331
      }, {
        filename: "/lib/python3.15/test/test_importlib/import_/__init__.py",
        start: 36416331,
        end: 36416473
      }, {
        filename: "/lib/python3.15/test/test_importlib/import_/__main__.py",
        start: 36416473,
        end: 36416531
      }, {
        filename: "/lib/python3.15/test/test_importlib/import_/test___loader__.py",
        start: 36416531,
        end: 36417291
      }, {
        filename: "/lib/python3.15/test/test_importlib/import_/test___package__.py",
        start: 36417291,
        end: 36422631
      }, {
        filename: "/lib/python3.15/test/test_importlib/import_/test_api.py",
        start: 36422631,
        end: 36425992
      }, {
        filename: "/lib/python3.15/test/test_importlib/import_/test_caching.py",
        start: 36425992,
        end: 36429837
      }, {
        filename: "/lib/python3.15/test/test_importlib/import_/test_fromlist.py",
        start: 36429837,
        end: 36437301
      }, {
        filename: "/lib/python3.15/test/test_importlib/import_/test_helpers.py",
        start: 36437301,
        end: 36443860
      }, {
        filename: "/lib/python3.15/test/test_importlib/import_/test_meta_path.py",
        start: 36443860,
        end: 36448331
      }, {
        filename: "/lib/python3.15/test/test_importlib/import_/test_packages.py",
        start: 36448331,
        end: 36452912
      }, {
        filename: "/lib/python3.15/test/test_importlib/import_/test_path.py",
        start: 36452912,
        end: 36463041
      }, {
        filename: "/lib/python3.15/test/test_importlib/import_/test_relative_imports.py",
        start: 36463041,
        end: 36473063
      }, {
        filename: "/lib/python3.15/test/test_importlib/metadata/__init__.py",
        start: 36473063,
        end: 36473063
      }, {
        filename: "/lib/python3.15/test/test_importlib/metadata/_context.py",
        start: 36473063,
        end: 36473345
      }, {
        filename: "/lib/python3.15/test/test_importlib/metadata/_path.py",
        start: 36473345,
        end: 36476484
      }, {
        filename: "/lib/python3.15/test/test_importlib/metadata/data/__init__.py",
        start: 36476484,
        end: 36476484
      }, {
        filename: "/lib/python3.15/test/test_importlib/metadata/data/example-21.12-py3-none-any.whl",
        start: 36476484,
        end: 36477939
      }, {
        filename: "/lib/python3.15/test/test_importlib/metadata/data/example-21.12-py3.6.egg",
        start: 36477939,
        end: 36479436
      }, {
        filename: "/lib/python3.15/test/test_importlib/metadata/data/example2-1.0.0-py3-none-any.whl",
        start: 36479436,
        end: 36480603
      }, {
        filename: "/lib/python3.15/test/test_importlib/metadata/data/sources/example/example/__init__.py",
        start: 36480603,
        end: 36480636
      }, {
        filename: "/lib/python3.15/test/test_importlib/metadata/data/sources/example/setup.py",
        start: 36480636,
        end: 36480886
      }, {
        filename: "/lib/python3.15/test/test_importlib/metadata/data/sources/example2/example2/__init__.py",
        start: 36480886,
        end: 36480919
      }, {
        filename: "/lib/python3.15/test/test_importlib/metadata/data/sources/example2/pyproject.toml",
        start: 36480919,
        end: 36481079
      }, {
        filename: "/lib/python3.15/test/test_importlib/metadata/fixtures.py",
        start: 36481079,
        end: 36492802
      }, {
        filename: "/lib/python3.15/test/test_importlib/metadata/stubs.py",
        start: 36492802,
        end: 36493035
      }, {
        filename: "/lib/python3.15/test/test_importlib/metadata/test_api.py",
        start: 36493035,
        end: 36503805
      }, {
        filename: "/lib/python3.15/test/test_importlib/metadata/test_main.py",
        start: 36503805,
        end: 36520149
      }, {
        filename: "/lib/python3.15/test/test_importlib/metadata/test_zip.py",
        start: 36520149,
        end: 36521944
      }, {
        filename: "/lib/python3.15/test/test_importlib/namespace_pkgs/both_portions/foo/one.py",
        start: 36521944,
        end: 36521975
      }, {
        filename: "/lib/python3.15/test/test_importlib/namespace_pkgs/both_portions/foo/two.py",
        start: 36521975,
        end: 36522006
      }, {
        filename: "/lib/python3.15/test/test_importlib/namespace_pkgs/foo/README.md",
        start: 36522006,
        end: 36522100
      }, {
        filename: "/lib/python3.15/test/test_importlib/namespace_pkgs/missing_directory.zip",
        start: 36522100,
        end: 36522615
      }, {
        filename: "/lib/python3.15/test/test_importlib/namespace_pkgs/module_and_namespace_package/a_test.py",
        start: 36522615,
        end: 36522634
      }, {
        filename: "/lib/python3.15/test/test_importlib/namespace_pkgs/module_and_namespace_package/a_test/empty",
        start: 36522634,
        end: 36522634
      }, {
        filename: "/lib/python3.15/test/test_importlib/namespace_pkgs/nested_portion1.zip",
        start: 36522634,
        end: 36523190
      }, {
        filename: "/lib/python3.15/test/test_importlib/namespace_pkgs/not_a_namespace_pkg/foo/__init__.py",
        start: 36523190,
        end: 36523190
      }, {
        filename: "/lib/python3.15/test/test_importlib/namespace_pkgs/not_a_namespace_pkg/foo/one.py",
        start: 36523190,
        end: 36523216
      }, {
        filename: "/lib/python3.15/test/test_importlib/namespace_pkgs/portion1/foo/one.py",
        start: 36523216,
        end: 36523242
      }, {
        filename: "/lib/python3.15/test/test_importlib/namespace_pkgs/portion2/foo/two.py",
        start: 36523242,
        end: 36523268
      }, {
        filename: "/lib/python3.15/test/test_importlib/namespace_pkgs/project1/parent/child/one.py",
        start: 36523268,
        end: 36523294
      }, {
        filename: "/lib/python3.15/test/test_importlib/namespace_pkgs/project2/parent/child/two.py",
        start: 36523294,
        end: 36523320
      }, {
        filename: "/lib/python3.15/test/test_importlib/namespace_pkgs/project3/parent/child/three.py",
        start: 36523320,
        end: 36523348
      }, {
        filename: "/lib/python3.15/test/test_importlib/namespace_pkgs/top_level_portion1.zip",
        start: 36523348,
        end: 36523680
      }, {
        filename: "/lib/python3.15/test/test_importlib/partial/cfimport.py",
        start: 36523680,
        end: 36524505
      }, {
        filename: "/lib/python3.15/test/test_importlib/partial/pool_in_threads.py",
        start: 36524505,
        end: 36524964
      }, {
        filename: "/lib/python3.15/test/test_importlib/resources/__init__.py",
        start: 36524964,
        end: 36524964
      }, {
        filename: "/lib/python3.15/test/test_importlib/resources/_path.py",
        start: 36524964,
        end: 36527252
      }, {
        filename: "/lib/python3.15/test/test_importlib/resources/test_compatibilty_files.py",
        start: 36527252,
        end: 36530558
      }, {
        filename: "/lib/python3.15/test/test_importlib/resources/test_contents.py",
        start: 36530558,
        end: 36531387
      }, {
        filename: "/lib/python3.15/test/test_importlib/resources/test_custom.py",
        start: 36531387,
        end: 36532636
      }, {
        filename: "/lib/python3.15/test/test_importlib/resources/test_files.py",
        start: 36532636,
        end: 36538062
      }, {
        filename: "/lib/python3.15/test/test_importlib/resources/test_functional.py",
        start: 36538062,
        end: 36546685
      }, {
        filename: "/lib/python3.15/test/test_importlib/resources/test_open.py",
        start: 36546685,
        end: 36549358
      }, {
        filename: "/lib/python3.15/test/test_importlib/resources/test_path.py",
        start: 36549358,
        end: 36551300
      }, {
        filename: "/lib/python3.15/test/test_importlib/resources/test_read.py",
        start: 36551300,
        end: 36554317
      }, {
        filename: "/lib/python3.15/test/test_importlib/resources/test_reader.py",
        start: 36554317,
        end: 36558962
      }, {
        filename: "/lib/python3.15/test/test_importlib/resources/test_resource.py",
        start: 36558962,
        end: 36566619
      }, {
        filename: "/lib/python3.15/test/test_importlib/resources/util.py",
        start: 36566619,
        end: 36572720
      }, {
        filename: "/lib/python3.15/test/test_importlib/resources/zip.py",
        start: 36572720,
        end: 36573293
      }, {
        filename: "/lib/python3.15/test/test_importlib/source/__init__.py",
        start: 36573293,
        end: 36573435
      }, {
        filename: "/lib/python3.15/test/test_importlib/source/__main__.py",
        start: 36573435,
        end: 36573493
      }, {
        filename: "/lib/python3.15/test/test_importlib/source/test_case_sensitivity.py",
        start: 36573493,
        end: 36576594
      }, {
        filename: "/lib/python3.15/test/test_importlib/source/test_file_loader.py",
        start: 36576594,
        end: 36599602
      }, {
        filename: "/lib/python3.15/test/test_importlib/source/test_finder.py",
        start: 36599602,
        end: 36607669
      }, {
        filename: "/lib/python3.15/test/test_importlib/source/test_path_hook.py",
        start: 36607669,
        end: 36608487
      }, {
        filename: "/lib/python3.15/test/test_importlib/source/test_source_encoding.py",
        start: 36608487,
        end: 36613119
      }, {
        filename: "/lib/python3.15/test/test_importlib/test_abc.py",
        start: 36613119,
        end: 36640292
      }, {
        filename: "/lib/python3.15/test/test_importlib/test_api.py",
        start: 36640292,
        end: 36660487
      }, {
        filename: "/lib/python3.15/test/test_importlib/test_lazy.py",
        start: 36660487,
        end: 36669540
      }, {
        filename: "/lib/python3.15/test/test_importlib/test_locks.py",
        start: 36669540,
        end: 36674353
      }, {
        filename: "/lib/python3.15/test/test_importlib/test_namespace_pkgs.py",
        start: 36674353,
        end: 36686974
      }, {
        filename: "/lib/python3.15/test/test_importlib/test_pkg_import.py",
        start: 36686974,
        end: 36689727
      }, {
        filename: "/lib/python3.15/test/test_importlib/test_spec.py",
        start: 36689727,
        end: 36716e3
      }, {
        filename: "/lib/python3.15/test/test_importlib/test_threaded_import.py",
        start: 36716e3,
        end: 36725947
      }, {
        filename: "/lib/python3.15/test/test_importlib/test_util.py",
        start: 36725947,
        end: 36759846
      }, {
        filename: "/lib/python3.15/test/test_importlib/test_windows.py",
        start: 36759846,
        end: 36768152
      }, {
        filename: "/lib/python3.15/test/test_importlib/threaded_import_hangers.py",
        start: 36768152,
        end: 36769636
      }, {
        filename: "/lib/python3.15/test/test_importlib/util.py",
        start: 36769636,
        end: 36782924
      }, {
        filename: "/lib/python3.15/test/test_index.py",
        start: 36782924,
        end: 36791496
      }, {
        filename: "/lib/python3.15/test/test_inspect/__init__.py",
        start: 36791496,
        end: 36791628
      }, {
        filename: "/lib/python3.15/test/test_inspect/inspect_deferred_annotations.py",
        start: 36791628,
        end: 36791658
      }, {
        filename: "/lib/python3.15/test/test_inspect/inspect_fodder.py",
        start: 36791658,
        end: 36793774
      }, {
        filename: "/lib/python3.15/test/test_inspect/inspect_fodder2.py",
        start: 36793774,
        end: 36799575
      }, {
        filename: "/lib/python3.15/test/test_inspect/inspect_fodder3.py",
        start: 36799575,
        end: 36800476
      }, {
        filename: "/lib/python3.15/test/test_inspect/inspect_stock_annotations.py",
        start: 36800476,
        end: 36800985
      }, {
        filename: "/lib/python3.15/test/test_inspect/inspect_stringized_annotations.py",
        start: 36800985,
        end: 36801597
      }, {
        filename: "/lib/python3.15/test/test_inspect/inspect_stringized_annotations_2.py",
        start: 36801597,
        end: 36801657
      }, {
        filename: "/lib/python3.15/test/test_inspect/inspect_stringized_annotations_pep695.py",
        start: 36801657,
        end: 36803315
      }, {
        filename: "/lib/python3.15/test/test_inspect/test_inspect.py",
        start: 36803315,
        end: 37060452
      }, {
        filename: "/lib/python3.15/test/test_int.py",
        start: 37060452,
        end: 37096482
      }, {
        filename: "/lib/python3.15/test/test_int_literal.py",
        start: 37096482,
        end: 37103535
      }, {
        filename: "/lib/python3.15/test/test_interpreters/__init__.py",
        start: 37103535,
        end: 37103775
      }, {
        filename: "/lib/python3.15/test/test_interpreters/__main__.py",
        start: 37103775,
        end: 37103833
      }, {
        filename: "/lib/python3.15/test/test_interpreters/test_api.py",
        start: 37103833,
        end: 37191232
      }, {
        filename: "/lib/python3.15/test/test_interpreters/test_channels.py",
        start: 37191232,
        end: 37211241
      }, {
        filename: "/lib/python3.15/test/test_interpreters/test_lifecycle.py",
        start: 37211241,
        end: 37217767
      }, {
        filename: "/lib/python3.15/test/test_interpreters/test_queues.py",
        start: 37217767,
        end: 37240322
      }, {
        filename: "/lib/python3.15/test/test_interpreters/test_stress.py",
        start: 37240322,
        end: 37243401
      }, {
        filename: "/lib/python3.15/test/test_interpreters/utils.py",
        start: 37243401,
        end: 37263850
      }, {
        filename: "/lib/python3.15/test/test_io/__init__.py",
        start: 37263850,
        end: 37264957
      }, {
        filename: "/lib/python3.15/test/test_io/__main__.py",
        start: 37264957,
        end: 37265015
      }, {
        filename: "/lib/python3.15/test/test_io/test_bufferedio.py",
        start: 37265015,
        end: 37322013
      }, {
        filename: "/lib/python3.15/test/test_io/test_file.py",
        start: 37322013,
        end: 37334464
      }, {
        filename: "/lib/python3.15/test/test_io/test_fileio.py",
        start: 37334464,
        end: 37361022
      }, {
        filename: "/lib/python3.15/test/test_io/test_general.py",
        start: 37361022,
        end: 37416004
      }, {
        filename: "/lib/python3.15/test/test_io/test_largefile.py",
        start: 37416004,
        end: 37427181
      }, {
        filename: "/lib/python3.15/test/test_io/test_memoryio.py",
        start: 37427181,
        end: 37461195
      }, {
        filename: "/lib/python3.15/test/test_io/test_signals.py",
        start: 37461195,
        end: 37471866
      }, {
        filename: "/lib/python3.15/test/test_io/test_textio.py",
        start: 37471866,
        end: 37538437
      }, {
        filename: "/lib/python3.15/test/test_io/test_univnewlines.py",
        start: 37538437,
        end: 37542384
      }, {
        filename: "/lib/python3.15/test/test_io/utils.py",
        start: 37542384,
        end: 37550143
      }, {
        filename: "/lib/python3.15/test/test_ioctl.py",
        start: 37550143,
        end: 37558445
      }, {
        filename: "/lib/python3.15/test/test_ipaddress.py",
        start: 37558445,
        end: 37691221
      }, {
        filename: "/lib/python3.15/test/test_isinstance.py",
        start: 37691221,
        end: 37704731
      }, {
        filename: "/lib/python3.15/test/test_iter.py",
        start: 37704731,
        end: 37743870
      }, {
        filename: "/lib/python3.15/test/test_iterlen.py",
        start: 37743870,
        end: 37751136
      }, {
        filename: "/lib/python3.15/test/test_itertools.py",
        start: 37751136,
        end: 37852579
      }, {
        filename: "/lib/python3.15/test/test_json/__init__.py",
        start: 37852579,
        end: 37855103
      }, {
        filename: "/lib/python3.15/test/test_json/__main__.py",
        start: 37855103,
        end: 37855174
      }, {
        filename: "/lib/python3.15/test/test_json/test_decode.py",
        start: 37855174,
        end: 37860542
      }, {
        filename: "/lib/python3.15/test/test_json/test_default.py",
        start: 37860542,
        end: 37861857
      }, {
        filename: "/lib/python3.15/test/test_json/test_dump.py",
        start: 37861857,
        end: 37864619
      }, {
        filename: "/lib/python3.15/test/test_json/test_encode_basestring_ascii.py",
        start: 37864619,
        end: 37866756
      }, {
        filename: "/lib/python3.15/test/test_json/test_enum.py",
        start: 37866756,
        end: 37870790
      }, {
        filename: "/lib/python3.15/test/test_json/test_fail.py",
        start: 37870790,
        end: 37880899
      }, {
        filename: "/lib/python3.15/test/test_json/test_float.py",
        start: 37880899,
        end: 37882197
      }, {
        filename: "/lib/python3.15/test/test_json/test_indent.py",
        start: 37882197,
        end: 37884021
      }, {
        filename: "/lib/python3.15/test/test_json/test_pass1.py",
        start: 37884021,
        end: 37885859
      }, {
        filename: "/lib/python3.15/test/test_json/test_pass2.py",
        start: 37885859,
        end: 37886308
      }, {
        filename: "/lib/python3.15/test/test_json/test_pass3.py",
        start: 37886308,
        end: 37886853
      }, {
        filename: "/lib/python3.15/test/test_json/test_recursion.py",
        start: 37886853,
        end: 37890930
      }, {
        filename: "/lib/python3.15/test/test_json/test_scanstring.py",
        start: 37890930,
        end: 37895909
      }, {
        filename: "/lib/python3.15/test/test_json/test_separators.py",
        start: 37895909,
        end: 37897228
      }, {
        filename: "/lib/python3.15/test/test_json/test_speedups.py",
        start: 37897228,
        end: 37900556
      }, {
        filename: "/lib/python3.15/test/test_json/test_tool.py",
        start: 37900556,
        end: 37911207
      }, {
        filename: "/lib/python3.15/test/test_json/test_unicode.py",
        start: 37911207,
        end: 37917226
      }, {
        filename: "/lib/python3.15/test/test_keyword.py",
        start: 37917226,
        end: 37919276
      }, {
        filename: "/lib/python3.15/test/test_keywordonlyarg.py",
        start: 37919276,
        end: 37926334
      }, {
        filename: "/lib/python3.15/test/test_kqueue.py",
        start: 37926334,
        end: 37936031
      }, {
        filename: "/lib/python3.15/test/test_launcher.py",
        start: 37936031,
        end: 37967289
      }, {
        filename: "/lib/python3.15/test/test_linecache.py",
        start: 37967289,
        end: 37983478
      }, {
        filename: "/lib/python3.15/test/test_list.py",
        start: 37983478,
        end: 37995859
      }, {
        filename: "/lib/python3.15/test/test_listcomps.py",
        start: 37995859,
        end: 38019976
      }, {
        filename: "/lib/python3.15/test/test_lltrace.py",
        start: 38019976,
        end: 38023771
      }, {
        filename: "/lib/python3.15/test/test_locale.py",
        start: 38023771,
        end: 38056014
      }, {
        filename: "/lib/python3.15/test/test_logging.py",
        start: 38056014,
        end: 38326159
      }, {
        filename: "/lib/python3.15/test/test_long.py",
        start: 38326159,
        end: 38393834
      }, {
        filename: "/lib/python3.15/test/test_longexp.py",
        start: 38393834,
        end: 38394067
      }, {
        filename: "/lib/python3.15/test/test_lzma.py",
        start: 38394067,
        end: 38492166
      }, {
        filename: "/lib/python3.15/test/test_mailbox.py",
        start: 38492166,
        end: 38593607
      }, {
        filename: "/lib/python3.15/test/test_marshal.py",
        start: 38593607,
        end: 38619336
      }, {
        filename: "/lib/python3.15/test/test_math.py",
        start: 38619336,
        end: 38743159
      }, {
        filename: "/lib/python3.15/test/test_math_integer.py",
        start: 38743159,
        end: 38758246
      }, {
        filename: "/lib/python3.15/test/test_math_property.py",
        start: 38758246,
        end: 38759427
      }, {
        filename: "/lib/python3.15/test/test_memoryview.py",
        start: 38759427,
        end: 38786250
      }, {
        filename: "/lib/python3.15/test/test_metaclass.py",
        start: 38786250,
        end: 38793476
      }, {
        filename: "/lib/python3.15/test/test_mimetypes.py",
        start: 38793476,
        end: 38815780
      }, {
        filename: "/lib/python3.15/test/test_minidom.py",
        start: 38815780,
        end: 38889540
      }, {
        filename: "/lib/python3.15/test/test_mmap.py",
        start: 38889540,
        end: 38937761
      }, {
        filename: "/lib/python3.15/test/test_module/__init__.py",
        start: 38937761,
        end: 38952496
      }, {
        filename: "/lib/python3.15/test/test_module/bad_getattr.py",
        start: 38952496,
        end: 38952557
      }, {
        filename: "/lib/python3.15/test/test_module/bad_getattr2.py",
        start: 38952557,
        end: 38952634
      }, {
        filename: "/lib/python3.15/test/test_module/bad_getattr3.py",
        start: 38952634,
        end: 38952773
      }, {
        filename: "/lib/python3.15/test/test_module/final_a.py",
        start: 38952773,
        end: 38953208
      }, {
        filename: "/lib/python3.15/test/test_module/final_b.py",
        start: 38953208,
        end: 38953643
      }, {
        filename: "/lib/python3.15/test/test_module/good_getattr.py",
        start: 38953643,
        end: 38953841
      }, {
        filename: "/lib/python3.15/test/test_modulefinder.py",
        start: 38953841,
        end: 38966684
      }, {
        filename: "/lib/python3.15/test/test_monitoring.py",
        start: 38966684,
        end: 39048636
      }, {
        filename: "/lib/python3.15/test/test_msvcrt.py",
        start: 39048636,
        end: 39052111
      }, {
        filename: "/lib/python3.15/test/test_multibytecodec.py",
        start: 39052111,
        end: 39068423
      }, {
        filename: "/lib/python3.15/test/test_multiprocessing_fork/__init__.py",
        start: 39068423,
        end: 39068965
      }, {
        filename: "/lib/python3.15/test/test_multiprocessing_fork/test_manager.py",
        start: 39068965,
        end: 39069167
      }, {
        filename: "/lib/python3.15/test/test_multiprocessing_fork/test_misc.py",
        start: 39069167,
        end: 39069368
      }, {
        filename: "/lib/python3.15/test/test_multiprocessing_fork/test_processes.py",
        start: 39069368,
        end: 39069572
      }, {
        filename: "/lib/python3.15/test/test_multiprocessing_fork/test_threads.py",
        start: 39069572,
        end: 39069774
      }, {
        filename: "/lib/python3.15/test/test_multiprocessing_forkserver/__init__.py",
        start: 39069774,
        end: 39070112
      }, {
        filename: "/lib/python3.15/test/test_multiprocessing_forkserver/test_manager.py",
        start: 39070112,
        end: 39070320
      }, {
        filename: "/lib/python3.15/test/test_multiprocessing_forkserver/test_misc.py",
        start: 39070320,
        end: 39070527
      }, {
        filename: "/lib/python3.15/test/test_multiprocessing_forkserver/test_processes.py",
        start: 39070527,
        end: 39070737
      }, {
        filename: "/lib/python3.15/test/test_multiprocessing_forkserver/test_threads.py",
        start: 39070737,
        end: 39070945
      }, {
        filename: "/lib/python3.15/test/test_multiprocessing_main_handling.py",
        start: 39070945,
        end: 39082703
      }, {
        filename: "/lib/python3.15/test/test_multiprocessing_spawn/__init__.py",
        start: 39082703,
        end: 39082931
      }, {
        filename: "/lib/python3.15/test/test_multiprocessing_spawn/test_manager.py",
        start: 39082931,
        end: 39083134
      }, {
        filename: "/lib/python3.15/test/test_multiprocessing_spawn/test_misc.py",
        start: 39083134,
        end: 39083336
      }, {
        filename: "/lib/python3.15/test/test_multiprocessing_spawn/test_processes.py",
        start: 39083336,
        end: 39083541
      }, {
        filename: "/lib/python3.15/test/test_multiprocessing_spawn/test_threads.py",
        start: 39083541,
        end: 39083744
      }, {
        filename: "/lib/python3.15/test/test_named_expressions.py",
        start: 39083744,
        end: 39114077
      }, {
        filename: "/lib/python3.15/test/test_netrc.py",
        start: 39114077,
        end: 39126458
      }, {
        filename: "/lib/python3.15/test/test_ntpath.py",
        start: 39126458,
        end: 39210216
      }, {
        filename: "/lib/python3.15/test/test_nturl2path.py",
        start: 39210216,
        end: 39215503
      }, {
        filename: "/lib/python3.15/test/test_numeric_tower.py",
        start: 39215503,
        end: 39223691
      }, {
        filename: "/lib/python3.15/test/test_opcache.py",
        start: 39223691,
        end: 39280241
      }, {
        filename: "/lib/python3.15/test/test_opcodes.py",
        start: 39280241,
        end: 39284033
      }, {
        filename: "/lib/python3.15/test/test_openpty.py",
        start: 39284033,
        end: 39284633
      }, {
        filename: "/lib/python3.15/test/test_operator.py",
        start: 39284633,
        end: 39314356
      }, {
        filename: "/lib/python3.15/test/test_optimizer.py",
        start: 39314356,
        end: 39317026
      }, {
        filename: "/lib/python3.15/test/test_optparse.py",
        start: 39317026,
        end: 39380410
      }, {
        filename: "/lib/python3.15/test/test_ordered_dict.py",
        start: 39380410,
        end: 39421308
      }, {
        filename: "/lib/python3.15/test/test_os/__init__.py",
        start: 39421308,
        end: 39421456
      }, {
        filename: "/lib/python3.15/test/test_os/test_os.py",
        start: 39421456,
        end: 39620846
      }, {
        filename: "/lib/python3.15/test/test_os/test_posix.py",
        start: 39620846,
        end: 39727913
      }, {
        filename: "/lib/python3.15/test/test_os/test_windows.py",
        start: 39727913,
        end: 39750934
      }, {
        filename: "/lib/python3.15/test/test_os/utils.py",
        start: 39750934,
        end: 39751047
      }, {
        filename: "/lib/python3.15/test/test_osx_env.py",
        start: 39751047,
        end: 39752385
      }, {
        filename: "/lib/python3.15/test/test_pathlib/__init__.py",
        start: 39752385,
        end: 39752527
      }, {
        filename: "/lib/python3.15/test/test_pathlib/support/__init__.py",
        start: 39752527,
        end: 39752618
      }, {
        filename: "/lib/python3.15/test/test_pathlib/support/lexical_path.py",
        start: 39752618,
        end: 39753756
      }, {
        filename: "/lib/python3.15/test/test_pathlib/support/local_path.py",
        start: 39753756,
        end: 39759104
      }, {
        filename: "/lib/python3.15/test/test_pathlib/support/zip_path.py",
        start: 39759104,
        end: 39770034
      }, {
        filename: "/lib/python3.15/test/test_pathlib/test_copy.py",
        start: 39770034,
        end: 39777642
      }, {
        filename: "/lib/python3.15/test/test_pathlib/test_join.py",
        start: 39777642,
        end: 39797186
      }, {
        filename: "/lib/python3.15/test/test_pathlib/test_join_posix.py",
        start: 39797186,
        end: 39798398
      }, {
        filename: "/lib/python3.15/test/test_pathlib/test_join_windows.py",
        start: 39798398,
        end: 39811071
      }, {
        filename: "/lib/python3.15/test/test_pathlib/test_pathlib.py",
        start: 39811071,
        end: 39963349
      }, {
        filename: "/lib/python3.15/test/test_pathlib/test_read.py",
        start: 39963349,
        end: 39979144
      }, {
        filename: "/lib/python3.15/test/test_pathlib/test_write.py",
        start: 39979144,
        end: 39984395
      }, {
        filename: "/lib/python3.15/test/test_patma.py",
        start: 39984395,
        end: 40081493
      }, {
        filename: "/lib/python3.15/test/test_pdb.py",
        start: 40081493,
        end: 40251404
      }, {
        filename: "/lib/python3.15/test/test_peepholer.py",
        start: 40251404,
        end: 40346016
      }, {
        filename: "/lib/python3.15/test/test_peg_generator/__init__.py",
        start: 40346016,
        end: 40346310
      }, {
        filename: "/lib/python3.15/test/test_peg_generator/__main__.py",
        start: 40346310,
        end: 40346368
      }, {
        filename: "/lib/python3.15/test/test_peg_generator/test_c_parser.py",
        start: 40346368,
        end: 40366089
      }, {
        filename: "/lib/python3.15/test/test_peg_generator/test_first_sets.py",
        start: 40366089,
        end: 40374060
      }, {
        filename: "/lib/python3.15/test/test_peg_generator/test_grammar_validator.py",
        start: 40374060,
        end: 40376351
      }, {
        filename: "/lib/python3.15/test/test_peg_generator/test_pegen.py",
        start: 40376351,
        end: 40417096
      }, {
        filename: "/lib/python3.15/test/test_pep646_syntax.py",
        start: 40417096,
        end: 40425078
      }, {
        filename: "/lib/python3.15/test/test_perf_profiler.py",
        start: 40425078,
        end: 40445404
      }, {
        filename: "/lib/python3.15/test/test_perfmaps.py",
        start: 40445404,
        end: 40446420
      }, {
        filename: "/lib/python3.15/test/test_pickle.py",
        start: 40446420,
        end: 40475451
      }, {
        filename: "/lib/python3.15/test/test_picklebuffer.py",
        start: 40475451,
        end: 40480560
      }, {
        filename: "/lib/python3.15/test/test_pickletools.py",
        start: 40480560,
        end: 40505122
      }, {
        filename: "/lib/python3.15/test/test_pkg.py",
        start: 40505122,
        end: 40514787
      }, {
        filename: "/lib/python3.15/test/test_pkgutil.py",
        start: 40514787,
        end: 40539370
      }, {
        filename: "/lib/python3.15/test/test_platform.py",
        start: 40539370,
        end: 40572100
      }, {
        filename: "/lib/python3.15/test/test_plistlib.py",
        start: 40572100,
        end: 40619964
      }, {
        filename: "/lib/python3.15/test/test_poll.py",
        start: 40619964,
        end: 40627638
      }, {
        filename: "/lib/python3.15/test/test_popen.py",
        start: 40627638,
        end: 40630058
      }, {
        filename: "/lib/python3.15/test/test_poplib.py",
        start: 40630058,
        end: 40648491
      }, {
        filename: "/lib/python3.15/test/test_positional_only_arg.py",
        start: 40648491,
        end: 40667566
      }, {
        filename: "/lib/python3.15/test/test_posixpath.py",
        start: 40667566,
        end: 40728808
      }, {
        filename: "/lib/python3.15/test/test_pow.py",
        start: 40728808,
        end: 40735346
      }, {
        filename: "/lib/python3.15/test/test_pprint.py",
        start: 40735346,
        end: 40789927
      }, {
        filename: "/lib/python3.15/test/test_print.py",
        start: 40789927,
        end: 40796823
      }, {
        filename: "/lib/python3.15/test/test_profile.py",
        start: 40796823,
        end: 40806158
      }, {
        filename: "/lib/python3.15/test/test_profiling/__init__.py",
        start: 40806158,
        end: 40806300
      }, {
        filename: "/lib/python3.15/test/test_profiling/__main__.py",
        start: 40806300,
        end: 40806358
      }, {
        filename: "/lib/python3.15/test/test_profiling/test_heatmap.py",
        start: 40806358,
        end: 40835554
      }, {
        filename: "/lib/python3.15/test/test_profiling/test_sampling_profiler/__init__.py",
        start: 40835554,
        end: 40835805
      }, {
        filename: "/lib/python3.15/test/test_profiling/test_sampling_profiler/_live_collector_helpers.py",
        start: 40835805,
        end: 40837741
      }, {
        filename: "/lib/python3.15/test/test_profiling/test_sampling_profiler/helpers.py",
        start: 40837741,
        end: 40843121
      }, {
        filename: "/lib/python3.15/test/test_profiling/test_sampling_profiler/mocks.py",
        start: 40843121,
        end: 40846205
      }, {
        filename: "/lib/python3.15/test/test_profiling/test_sampling_profiler/test_advanced.py",
        start: 40846205,
        end: 40854181
      }, {
        filename: "/lib/python3.15/test/test_profiling/test_sampling_profiler/test_async.py",
        start: 40854181,
        end: 40884805
      }, {
        filename: "/lib/python3.15/test/test_profiling/test_sampling_profiler/test_children.py",
        start: 40884805,
        end: 40920482
      }, {
        filename: "/lib/python3.15/test/test_profiling/test_sampling_profiler/test_cli.py",
        start: 40920482,
        end: 40947630
      }, {
        filename: "/lib/python3.15/test/test_profiling/test_sampling_profiler/test_collectors.py",
        start: 40947630,
        end: 41016899
      }, {
        filename: "/lib/python3.15/test/test_profiling/test_sampling_profiler/test_integration.py",
        start: 41016899,
        end: 41052703
      }, {
        filename: "/lib/python3.15/test/test_profiling/test_sampling_profiler/test_live_collector_core.py",
        start: 41052703,
        end: 41081384
      }, {
        filename: "/lib/python3.15/test/test_profiling/test_sampling_profiler/test_live_collector_interaction.py",
        start: 41081384,
        end: 41128629
      }, {
        filename: "/lib/python3.15/test/test_profiling/test_sampling_profiler/test_live_collector_ui.py",
        start: 41128629,
        end: 41158774
      }, {
        filename: "/lib/python3.15/test/test_profiling/test_sampling_profiler/test_modes.py",
        start: 41158774,
        end: 41180261
      }, {
        filename: "/lib/python3.15/test/test_profiling/test_sampling_profiler/test_profiler.py",
        start: 41180261,
        end: 41205986
      }, {
        filename: "/lib/python3.15/test/test_profiling/test_sampling_profiler/test_trend_tracker.py",
        start: 41205986,
        end: 41209033
      }, {
        filename: "/lib/python3.15/test/test_profiling/test_tracing_profiler.py",
        start: 41209033,
        end: 41219326
      }, {
        filename: "/lib/python3.15/test/test_property.py",
        start: 41219326,
        end: 41239912
      }, {
        filename: "/lib/python3.15/test/test_pstats.py",
        start: 41239912,
        end: 41245633
      }, {
        filename: "/lib/python3.15/test/test_pty.py",
        start: 41245633,
        end: 41262377
      }, {
        filename: "/lib/python3.15/test/test_pulldom.py",
        start: 41262377,
        end: 41274993
      }, {
        filename: "/lib/python3.15/test/test_pwd.py",
        start: 41274993,
        end: 41279421
      }, {
        filename: "/lib/python3.15/test/test_py_compile.py",
        start: 41279421,
        end: 41291640
      }, {
        filename: "/lib/python3.15/test/test_pyclbr.py",
        start: 41291640,
        end: 41302607
      }, {
        filename: "/lib/python3.15/test/test_pydoc/__init__.py",
        start: 41302607,
        end: 41302739
      }, {
        filename: "/lib/python3.15/test/test_pydoc/module_none.py",
        start: 41302739,
        end: 41302857
      }, {
        filename: "/lib/python3.15/test/test_pydoc/pydoc_mod.py",
        start: 41302857,
        end: 41303857
      }, {
        filename: "/lib/python3.15/test/test_pydoc/pydocfodder.py",
        start: 41303857,
        end: 41309279
      }, {
        filename: "/lib/python3.15/test/test_pydoc/test_pydoc.py",
        start: 41309279,
        end: 41400276
      }, {
        filename: "/lib/python3.15/test/test_pyexpat.py",
        start: 41400276,
        end: 41444767
      }, {
        filename: "/lib/python3.15/test/test_pyrepl/__init__.py",
        start: 41444767,
        end: 41445009
      }, {
        filename: "/lib/python3.15/test/test_pyrepl/__main__.py",
        start: 41445009,
        end: 41445082
      }, {
        filename: "/lib/python3.15/test/test_pyrepl/eio_test_script.py",
        start: 41445082,
        end: 41448590
      }, {
        filename: "/lib/python3.15/test/test_pyrepl/support.py",
        start: 41448590,
        end: 41453318
      }, {
        filename: "/lib/python3.15/test/test_pyrepl/test_eventqueue.py",
        start: 41453318,
        end: 41459654
      }, {
        filename: "/lib/python3.15/test/test_pyrepl/test_input.py",
        start: 41459654,
        end: 41463146
      }, {
        filename: "/lib/python3.15/test/test_pyrepl/test_interact.py",
        start: 41463146,
        end: 41473097
      }, {
        filename: "/lib/python3.15/test/test_pyrepl/test_keymap.py",
        start: 41473097,
        end: 41478270
      }, {
        filename: "/lib/python3.15/test/test_pyrepl/test_pyrepl.py",
        start: 41478270,
        end: 41547988
      }, {
        filename: "/lib/python3.15/test/test_pyrepl/test_reader.py",
        start: 41547988,
        end: 41567592
      }, {
        filename: "/lib/python3.15/test/test_pyrepl/test_terminfo.py",
        start: 41567592,
        end: 41589938
      }, {
        filename: "/lib/python3.15/test/test_pyrepl/test_unix_console.py",
        start: 41589938,
        end: 41602312
      }, {
        filename: "/lib/python3.15/test/test_pyrepl/test_utils.py",
        start: 41602312,
        end: 41605801
      }, {
        filename: "/lib/python3.15/test/test_pyrepl/test_windows_console.py",
        start: 41605801,
        end: 41626204
      }, {
        filename: "/lib/python3.15/test/test_pystats.py",
        start: 41626204,
        end: 41632119
      }, {
        filename: "/lib/python3.15/test/test_queue.py",
        start: 41632119,
        end: 41666461
      }, {
        filename: "/lib/python3.15/test/test_quopri.py",
        start: 41666461,
        end: 41674518
      }, {
        filename: "/lib/python3.15/test/test_raise.py",
        start: 41674518,
        end: 41688869
      }, {
        filename: "/lib/python3.15/test/test_random.py",
        start: 41688869,
        end: 41749670
      }, {
        filename: "/lib/python3.15/test/test_range.py",
        start: 41749670,
        end: 41777308
      }, {
        filename: "/lib/python3.15/test/test_re.py",
        start: 41777308,
        end: 41927945
      }, {
        filename: "/lib/python3.15/test/test_readline.py",
        start: 41927945,
        end: 41946151
      }, {
        filename: "/lib/python3.15/test/test_regrtest.py",
        start: 41946151,
        end: 42046206
      }, {
        filename: "/lib/python3.15/test/test_remote_pdb.py",
        start: 42046206,
        end: 42104773
      }, {
        filename: "/lib/python3.15/test/test_repl.py",
        start: 42104773,
        end: 42118839
      }, {
        filename: "/lib/python3.15/test/test_reprlib.py",
        start: 42118839,
        end: 42150431
      }, {
        filename: "/lib/python3.15/test/test_resource.py",
        start: 42150431,
        end: 42162734
      }, {
        filename: "/lib/python3.15/test/test_richcmp.py",
        start: 42162734,
        end: 42174756
      }, {
        filename: "/lib/python3.15/test/test_rlcompleter.py",
        start: 42174756,
        end: 42182901
      }, {
        filename: "/lib/python3.15/test/test_robotparser.py",
        start: 42182901,
        end: 42198872
      }, {
        filename: "/lib/python3.15/test/test_runpy.py",
        start: 42198872,
        end: 42235794
      }, {
        filename: "/lib/python3.15/test/test_samply_profiler.py",
        start: 42235794,
        end: 42243729
      }, {
        filename: "/lib/python3.15/test/test_sax.py",
        start: 42243729,
        end: 42300650
      }, {
        filename: "/lib/python3.15/test/test_sched.py",
        start: 42300650,
        end: 42308205
      }, {
        filename: "/lib/python3.15/test/test_scope.py",
        start: 42308205,
        end: 42330669
      }, {
        filename: "/lib/python3.15/test/test_script_helper.py",
        start: 42330669,
        end: 42336610
      }, {
        filename: "/lib/python3.15/test/test_secrets.py",
        start: 42336610,
        end: 42340991
      }, {
        filename: "/lib/python3.15/test/test_select.py",
        start: 42340991,
        end: 42344495
      }, {
        filename: "/lib/python3.15/test/test_selectors.py",
        start: 42344495,
        end: 42364846
      }, {
        filename: "/lib/python3.15/test/test_set.py",
        start: 42364846,
        end: 42438989
      }, {
        filename: "/lib/python3.15/test/test_setcomps.py",
        start: 42438989,
        end: 42444352
      }, {
        filename: "/lib/python3.15/test/test_shelve.py",
        start: 42444352,
        end: 42459989
      }, {
        filename: "/lib/python3.15/test/test_shlex.py",
        start: 42459989,
        end: 42474073
      }, {
        filename: "/lib/python3.15/test/test_shutil.py",
        start: 42474073,
        end: 42618554
      }, {
        filename: "/lib/python3.15/test/test_signal.py",
        start: 42618554,
        end: 42672386
      }, {
        filename: "/lib/python3.15/test/test_site.py",
        start: 42672386,
        end: 42709558
      }, {
        filename: "/lib/python3.15/test/test_slice.py",
        start: 42709558,
        end: 42719245
      }, {
        filename: "/lib/python3.15/test/test_smtplib.py",
        start: 42719245,
        end: 42783009
      }, {
        filename: "/lib/python3.15/test/test_smtpnet.py",
        start: 42783009,
        end: 42786195
      }, {
        filename: "/lib/python3.15/test/test_socket.py",
        start: 42786195,
        end: 43073917
      }, {
        filename: "/lib/python3.15/test/test_socketserver.py",
        start: 43073917,
        end: 43092926
      }, {
        filename: "/lib/python3.15/test/test_sort.py",
        start: 43092926,
        end: 43107750
      }, {
        filename: "/lib/python3.15/test/test_source_encoding.py",
        start: 43107750,
        end: 43127948
      }, {
        filename: "/lib/python3.15/test/test_sqlite3/__init__.py",
        start: 43127948,
        end: 43128561
      }, {
        filename: "/lib/python3.15/test/test_sqlite3/__main__.py",
        start: 43128561,
        end: 43128676
      }, {
        filename: "/lib/python3.15/test/test_sqlite3/test_backup.py",
        start: 43128676,
        end: 43134281
      }, {
        filename: "/lib/python3.15/test/test_sqlite3/test_cli.py",
        start: 43134281,
        end: 43151226
      }, {
        filename: "/lib/python3.15/test/test_sqlite3/test_dbapi.py",
        start: 43151226,
        end: 43227273
      }, {
        filename: "/lib/python3.15/test/test_sqlite3/test_dump.py",
        start: 43227273,
        end: 43236442
      }, {
        filename: "/lib/python3.15/test/test_sqlite3/test_factory.py",
        start: 43236442,
        end: 43248650
      }, {
        filename: "/lib/python3.15/test/test_sqlite3/test_hooks.py",
        start: 43248650,
        end: 43261560
      }, {
        filename: "/lib/python3.15/test/test_sqlite3/test_regression.py",
        start: 43261560,
        end: 43281047
      }, {
        filename: "/lib/python3.15/test/test_sqlite3/test_transactions.py",
        start: 43281047,
        end: 43301014
      }, {
        filename: "/lib/python3.15/test/test_sqlite3/test_types.py",
        start: 43301014,
        end: 43321363
      }, {
        filename: "/lib/python3.15/test/test_sqlite3/test_userfunctions.py",
        start: 43321363,
        end: 43350093
      }, {
        filename: "/lib/python3.15/test/test_sqlite3/util.py",
        start: 43350093,
        end: 43352780
      }, {
        filename: "/lib/python3.15/test/test_ssl.py",
        start: 43352780,
        end: 43598581
      }, {
        filename: "/lib/python3.15/test/test_stable_abi_ctypes.py",
        start: 43598581,
        end: 43626248
      }, {
        filename: "/lib/python3.15/test/test_startfile.py",
        start: 43626248,
        end: 43627984
      }, {
        filename: "/lib/python3.15/test/test_stat.py",
        start: 43627984,
        end: 43641310
      }, {
        filename: "/lib/python3.15/test/test_statistics.py",
        start: 43641310,
        end: 43775407
      }, {
        filename: "/lib/python3.15/test/test_str.py",
        start: 43775407,
        end: 43904908
      }, {
        filename: "/lib/python3.15/test/test_strftime.py",
        start: 43904908,
        end: 43912929
      }, {
        filename: "/lib/python3.15/test/test_string/__init__.py",
        start: 43912929,
        end: 43913071
      }, {
        filename: "/lib/python3.15/test/test_string/_support.py",
        start: 43913071,
        end: 43915458
      }, {
        filename: "/lib/python3.15/test/test_string/test_string.py",
        start: 43915458,
        end: 43938950
      }, {
        filename: "/lib/python3.15/test/test_string/test_templatelib.py",
        start: 43938950,
        end: 43946346
      }, {
        filename: "/lib/python3.15/test/test_string_literals.py",
        start: 43946346,
        end: 43961925
      }, {
        filename: "/lib/python3.15/test/test_stringprep.py",
        start: 43961925,
        end: 43965038
      }, {
        filename: "/lib/python3.15/test/test_strptime.py",
        start: 43965038,
        end: 44009020
      }, {
        filename: "/lib/python3.15/test/test_strtod.py",
        start: 44009020,
        end: 44029557
      }, {
        filename: "/lib/python3.15/test/test_struct.py",
        start: 44029557,
        end: 44071420
      }, {
        filename: "/lib/python3.15/test/test_structseq.py",
        start: 44071420,
        end: 44085902
      }, {
        filename: "/lib/python3.15/test/test_subclassinit.py",
        start: 44085902,
        end: 44094138
      }, {
        filename: "/lib/python3.15/test/test_subprocess.py",
        start: 44094138,
        end: 44269410
      }, {
        filename: "/lib/python3.15/test/test_sundry.py",
        start: 44269410,
        end: 44270500
      }, {
        filename: "/lib/python3.15/test/test_super.py",
        start: 44270500,
        end: 44289372
      }, {
        filename: "/lib/python3.15/test/test_support.py",
        start: 44289372,
        end: 44330058
      }, {
        filename: "/lib/python3.15/test/test_symtable.py",
        start: 44330058,
        end: 44357370
      }, {
        filename: "/lib/python3.15/test/test_syntax.py",
        start: 44357370,
        end: 44461291
      }, {
        filename: "/lib/python3.15/test/test_sys.py",
        start: 44461291,
        end: 44550755
      }, {
        filename: "/lib/python3.15/test/test_sys_setprofile.py",
        start: 44550755,
        end: 44567356
      }, {
        filename: "/lib/python3.15/test/test_sys_settrace.py",
        start: 44567356,
        end: 44655975
      }, {
        filename: "/lib/python3.15/test/test_sysconfig.py",
        start: 44655975,
        end: 44693415
      }, {
        filename: "/lib/python3.15/test/test_syslog.py",
        start: 44693415,
        end: 44698232
      }, {
        filename: "/lib/python3.15/test/test_tabnanny.py",
        start: 44698232,
        end: 44712843
      }, {
        filename: "/lib/python3.15/test/test_tarfile.py",
        start: 44712843,
        end: 44905919
      }, {
        filename: "/lib/python3.15/test/test_tcl.py",
        start: 44905919,
        end: 44937406
      }, {
        filename: "/lib/python3.15/test/test_tempfile.py",
        start: 44937406,
        end: 45014521
      }, {
        filename: "/lib/python3.15/test/test_termios.py",
        start: 45014521,
        end: 45028727
      }, {
        filename: "/lib/python3.15/test/test_textwrap.py",
        start: 45028727,
        end: 45073192
      }, {
        filename: "/lib/python3.15/test/test_thread.py",
        start: 45073192,
        end: 45087883
      }, {
        filename: "/lib/python3.15/test/test_thread_local_bytecode.py",
        start: 45087883,
        end: 45093286
      }, {
        filename: "/lib/python3.15/test/test_threadedtempfile.py",
        start: 45093286,
        end: 45095366
      }, {
        filename: "/lib/python3.15/test/test_threading.py",
        start: 45095366,
        end: 45187149
      }, {
        filename: "/lib/python3.15/test/test_threading_local.py",
        start: 45187149,
        end: 45194328
      }, {
        filename: "/lib/python3.15/test/test_threadsignals.py",
        start: 45194328,
        end: 45204436
      }, {
        filename: "/lib/python3.15/test/test_time.py",
        start: 45204436,
        end: 45250563
      }, {
        filename: "/lib/python3.15/test/test_timeit.py",
        start: 45250563,
        end: 45266023
      }, {
        filename: "/lib/python3.15/test/test_timeout.py",
        start: 45266023,
        end: 45276930
      }, {
        filename: "/lib/python3.15/test/test_tkinter/README",
        start: 45276930,
        end: 45277496
      }, {
        filename: "/lib/python3.15/test/test_tkinter/__init__.py",
        start: 45277496,
        end: 45278032
      }, {
        filename: "/lib/python3.15/test/test_tkinter/__main__.py",
        start: 45278032,
        end: 45278090
      }, {
        filename: "/lib/python3.15/test/test_tkinter/support.py",
        start: 45278090,
        end: 45282244
      }, {
        filename: "/lib/python3.15/test/test_tkinter/test_colorchooser.py",
        start: 45282244,
        end: 45284451
      }, {
        filename: "/lib/python3.15/test/test_tkinter/test_font.py",
        start: 45284451,
        end: 45291322
      }, {
        filename: "/lib/python3.15/test/test_tkinter/test_geometry_managers.py",
        start: 45291322,
        end: 45332507
      }, {
        filename: "/lib/python3.15/test/test_tkinter/test_images.py",
        start: 45332507,
        end: 45361304
      }, {
        filename: "/lib/python3.15/test/test_tkinter/test_loadtk.py",
        start: 45361304,
        end: 45362790
      }, {
        filename: "/lib/python3.15/test/test_tkinter/test_messagebox.py",
        start: 45362790,
        end: 45363920
      }, {
        filename: "/lib/python3.15/test/test_tkinter/test_misc.py",
        start: 45363920,
        end: 45413776
      }, {
        filename: "/lib/python3.15/test/test_tkinter/test_simpledialog.py",
        start: 45413776,
        end: 45414790
      }, {
        filename: "/lib/python3.15/test/test_tkinter/test_text.py",
        start: 45414790,
        end: 45424742
      }, {
        filename: "/lib/python3.15/test/test_tkinter/test_variables.py",
        start: 45424742,
        end: 45436477
      }, {
        filename: "/lib/python3.15/test/test_tkinter/test_widgets.py",
        start: 45436477,
        end: 45501611
      }, {
        filename: "/lib/python3.15/test/test_tkinter/widget_tests.py",
        start: 45501611,
        end: 45525966
      }, {
        filename: "/lib/python3.15/test/test_tokenize.py",
        start: 45525966,
        end: 45659148
      }, {
        filename: "/lib/python3.15/test/test_tomllib/__init__.py",
        start: 45659148,
        end: 45659543
      }, {
        filename: "/lib/python3.15/test/test_tomllib/__main__.py",
        start: 45659543,
        end: 45659603
      }, {
        filename: "/lib/python3.15/test/test_tomllib/burntsushi.py",
        start: 45659603,
        end: 45663627
      }, {
        filename: "/lib/python3.15/test/test_tomllib/data/invalid/array-missing-comma.toml",
        start: 45663627,
        end: 45663647
      }, {
        filename: "/lib/python3.15/test/test_tomllib/data/invalid/array-of-tables/overwrite-array-in-parent.toml",
        start: 45663647,
        end: 45663703
      }, {
        filename: "/lib/python3.15/test/test_tomllib/data/invalid/array-of-tables/overwrite-bool-with-aot.toml",
        start: 45663703,
        end: 45663715
      }, {
        filename: "/lib/python3.15/test/test_tomllib/data/invalid/array/file-end-after-val.toml",
        start: 45663715,
        end: 45663719
      }, {
        filename: "/lib/python3.15/test/test_tomllib/data/invalid/array/unclosed-after-item.toml",
        start: 45663719,
        end: 45663724
      }, {
        filename: "/lib/python3.15/test/test_tomllib/data/invalid/array/unclosed-empty.toml",
        start: 45663724,
        end: 45663727
      }, {
        filename: "/lib/python3.15/test/test_tomllib/data/invalid/basic-str-ends-in-escape.toml",
        start: 45663727,
        end: 45663755
      }, {
        filename: "/lib/python3.15/test/test_tomllib/data/invalid/boolean/invalid-false-casing.toml",
        start: 45663755,
        end: 45663764
      }, {
        filename: "/lib/python3.15/test/test_tomllib/data/invalid/boolean/invalid-true-casing.toml",
        start: 45663764,
        end: 45663772
      }, {
        filename: "/lib/python3.15/test/test_tomllib/data/invalid/dates-and-times/invalid-day.toml",
        start: 45663772,
        end: 45663818
      }, {
        filename: "/lib/python3.15/test/test_tomllib/data/invalid/dotted-keys/access-non-table.toml",
        start: 45663818,
        end: 45663838
      }, {
        filename: "/lib/python3.15/test/test_tomllib/data/invalid/dotted-keys/extend-defined-aot.toml",
        start: 45663838,
        end: 45663867
      }, {
        filename: "/lib/python3.15/test/test_tomllib/data/invalid/dotted-keys/extend-defined-table-with-subtable.toml",
        start: 45663867,
        end: 45663905
      }, {
        filename: "/lib/python3.15/test/test_tomllib/data/invalid/dotted-keys/extend-defined-table.toml",
        start: 45663905,
        end: 45663937
      }, {
        filename: "/lib/python3.15/test/test_tomllib/data/invalid/inline-table-missing-comma.toml",
        start: 45663937,
        end: 45663988
      }, {
        filename: "/lib/python3.15/test/test_tomllib/data/invalid/inline-table/define-twice-in-subtable.toml",
        start: 45663988,
        end: 45664033
      }, {
        filename: "/lib/python3.15/test/test_tomllib/data/invalid/inline-table/define-twice.toml",
        start: 45664033,
        end: 45664063
      }, {
        filename: "/lib/python3.15/test/test_tomllib/data/invalid/inline-table/file-end-after-key-val.toml",
        start: 45664063,
        end: 45664069
      }, {
        filename: "/lib/python3.15/test/test_tomllib/data/invalid/inline-table/mutate.toml",
        start: 45664069,
        end: 45664090
      }, {
        filename: "/lib/python3.15/test/test_tomllib/data/invalid/inline-table/override-val-in-table.toml",
        start: 45664090,
        end: 45664160
      }, {
        filename: "/lib/python3.15/test/test_tomllib/data/invalid/inline-table/override-val-with-array.toml",
        start: 45664160,
        end: 45664204
      }, {
        filename: "/lib/python3.15/test/test_tomllib/data/invalid/inline-table/override-val-with-table.toml",
        start: 45664204,
        end: 45664246
      }, {
        filename: "/lib/python3.15/test/test_tomllib/data/invalid/inline-table/overwrite-implicitly.toml",
        start: 45664246,
        end: 45664269
      }, {
        filename: "/lib/python3.15/test/test_tomllib/data/invalid/inline-table/overwrite-value-in-inner-array.toml",
        start: 45664269,
        end: 45664322
      }, {
        filename: "/lib/python3.15/test/test_tomllib/data/invalid/inline-table/overwrite-value-in-inner-table.toml",
        start: 45664322,
        end: 45664377
      }, {
        filename: "/lib/python3.15/test/test_tomllib/data/invalid/inline-table/unclosed-empty.toml",
        start: 45664377,
        end: 45664380
      }, {
        filename: "/lib/python3.15/test/test_tomllib/data/invalid/invalid-comment-char.toml",
        start: 45664380,
        end: 45664419
      }, {
        filename: "/lib/python3.15/test/test_tomllib/data/invalid/invalid-escaped-unicode.toml",
        start: 45664419,
        end: 45664446
      }, {
        filename: "/lib/python3.15/test/test_tomllib/data/invalid/invalid-hex.toml",
        start: 45664446,
        end: 45664464
      }, {
        filename: "/lib/python3.15/test/test_tomllib/data/invalid/keys-and-vals/ends-early-table-def.toml",
        start: 45664464,
        end: 45664474
      }, {
        filename: "/lib/python3.15/test/test_tomllib/data/invalid/keys-and-vals/ends-early.toml",
        start: 45664474,
        end: 45664479
      }, {
        filename: "/lib/python3.15/test/test_tomllib/data/invalid/keys-and-vals/no-value.toml",
        start: 45664479,
        end: 45664492
      }, {
        filename: "/lib/python3.15/test/test_tomllib/data/invalid/keys-and-vals/only-ws-after-dot.toml",
        start: 45664492,
        end: 45664495
      }, {
        filename: "/lib/python3.15/test/test_tomllib/data/invalid/keys-and-vals/overwrite-with-deep-table.toml",
        start: 45664495,
        end: 45664509
      }, {
        filename: "/lib/python3.15/test/test_tomllib/data/invalid/literal-str/unclosed.toml",
        start: 45664509,
        end: 45664523
      }, {
        filename: "/lib/python3.15/test/test_tomllib/data/invalid/missing-closing-double-square-bracket.toml",
        start: 45664523,
        end: 45664557
      }, {
        filename: "/lib/python3.15/test/test_tomllib/data/invalid/missing-closing-square-bracket.toml",
        start: 45664557,
        end: 45664591
      }, {
        filename: "/lib/python3.15/test/test_tomllib/data/invalid/multiline-basic-str/carriage-return.toml",
        start: 45664591,
        end: 45664660
      }, {
        filename: "/lib/python3.15/test/test_tomllib/data/invalid/multiline-basic-str/escape-only.toml",
        start: 45664660,
        end: 45664674
      }, {
        filename: "/lib/python3.15/test/test_tomllib/data/invalid/multiline-basic-str/file-ends-after-opening.toml",
        start: 45664674,
        end: 45664679
      }, {
        filename: "/lib/python3.15/test/test_tomllib/data/invalid/multiline-basic-str/last-line-escape.toml",
        start: 45664679,
        end: 45664708
      }, {
        filename: "/lib/python3.15/test/test_tomllib/data/invalid/multiline-basic-str/unclosed-ends-in-whitespace-escape.toml",
        start: 45664708,
        end: 45664728
      }, {
        filename: "/lib/python3.15/test/test_tomllib/data/invalid/multiline-literal-str/file-ends-after-opening.toml",
        start: 45664728,
        end: 45664733
      }, {
        filename: "/lib/python3.15/test/test_tomllib/data/invalid/multiline-literal-str/unclosed.toml",
        start: 45664733,
        end: 45664753
      }, {
        filename: "/lib/python3.15/test/test_tomllib/data/invalid/non-scalar-escaped.toml",
        start: 45664753,
        end: 45664763
      }, {
        filename: "/lib/python3.15/test/test_tomllib/data/invalid/table/eof-after-opening.toml",
        start: 45664763,
        end: 45664764
      }, {
        filename: "/lib/python3.15/test/test_tomllib/data/invalid/table/redefine-1.toml",
        start: 45664764,
        end: 45664789
      }, {
        filename: "/lib/python3.15/test/test_tomllib/data/invalid/table/redefine-2.toml",
        start: 45664789,
        end: 45664817
      }, {
        filename: "/lib/python3.15/test/test_tomllib/data/invalid/unclosed-multiline-string.toml",
        start: 45664817,
        end: 45664857
      }, {
        filename: "/lib/python3.15/test/test_tomllib/data/invalid/unclosed-string.toml",
        start: 45664857,
        end: 45664885
      }, {
        filename: "/lib/python3.15/test/test_tomllib/data/valid/apostrophes-in-literal-string.json",
        start: 45664885,
        end: 45664985
      }, {
        filename: "/lib/python3.15/test/test_tomllib/data/valid/apostrophes-in-literal-string.toml",
        start: 45664985,
        end: 45665053
      }, {
        filename: "/lib/python3.15/test/test_tomllib/data/valid/array/array-subtables.json",
        start: 45665053,
        end: 45665247
      }, {
        filename: "/lib/python3.15/test/test_tomllib/data/valid/array/array-subtables.toml",
        start: 45665247,
        end: 45665302
      }, {
        filename: "/lib/python3.15/test/test_tomllib/data/valid/array/open-parent-table.json",
        start: 45665302,
        end: 45665421
      }, {
        filename: "/lib/python3.15/test/test_tomllib/data/valid/array/open-parent-table.toml",
        start: 45665421,
        end: 45665490
      }, {
        filename: "/lib/python3.15/test/test_tomllib/data/valid/boolean.json",
        start: 45665490,
        end: 45665572
      }, {
        filename: "/lib/python3.15/test/test_tomllib/data/valid/boolean.toml",
        start: 45665572,
        end: 45665590
      }, {
        filename: "/lib/python3.15/test/test_tomllib/data/valid/dates-and-times/datetimes.json",
        start: 45665590,
        end: 45665729
      }, {
        filename: "/lib/python3.15/test/test_tomllib/data/valid/dates-and-times/datetimes.toml",
        start: 45665729,
        end: 45665787
      }, {
        filename: "/lib/python3.15/test/test_tomllib/data/valid/dates-and-times/localtime.json",
        start: 45665787,
        end: 45665844
      }, {
        filename: "/lib/python3.15/test/test_tomllib/data/valid/dates-and-times/localtime.toml",
        start: 45665844,
        end: 45665869
      }, {
        filename: "/lib/python3.15/test/test_tomllib/data/valid/empty-inline-table.json",
        start: 45665869,
        end: 45665883
      }, {
        filename: "/lib/python3.15/test/test_tomllib/data/valid/empty-inline-table.toml",
        start: 45665883,
        end: 45665918
      }, {
        filename: "/lib/python3.15/test/test_tomllib/data/valid/five-quotes.json",
        start: 45665918,
        end: 45666073
      }, {
        filename: "/lib/python3.15/test/test_tomllib/data/valid/five-quotes.toml",
        start: 45666073,
        end: 45666170
      }, {
        filename: "/lib/python3.15/test/test_tomllib/data/valid/hex-char.json",
        start: 45666170,
        end: 45666287
      }, {
        filename: "/lib/python3.15/test/test_tomllib/data/valid/hex-char.toml",
        start: 45666287,
        end: 45666323
      }, {
        filename: "/lib/python3.15/test/test_tomllib/data/valid/multiline-basic-str/ends-in-whitespace-escape.json",
        start: 45666323,
        end: 45666377
      }, {
        filename: "/lib/python3.15/test/test_tomllib/data/valid/multiline-basic-str/ends-in-whitespace-escape.toml",
        start: 45666377,
        end: 45666415
      }, {
        filename: "/lib/python3.15/test/test_tomllib/data/valid/no-newlines.json",
        start: 45666415,
        end: 45666418
      }, {
        filename: "/lib/python3.15/test/test_tomllib/data/valid/no-newlines.toml",
        start: 45666418,
        end: 45666442
      }, {
        filename: "/lib/python3.15/test/test_tomllib/data/valid/trailing-comma.json",
        start: 45666442,
        end: 45666532
      }, {
        filename: "/lib/python3.15/test/test_tomllib/data/valid/trailing-comma.toml",
        start: 45666532,
        end: 45666540
      }, {
        filename: "/lib/python3.15/test/test_tomllib/test_data.py",
        start: 45666540,
        end: 45668772
      }, {
        filename: "/lib/python3.15/test/test_tomllib/test_error.py",
        start: 45668772,
        end: 45672420
      }, {
        filename: "/lib/python3.15/test/test_tomllib/test_misc.py",
        start: 45672420,
        end: 45676703
      }, {
        filename: "/lib/python3.15/test/test_tools/__init__.py",
        start: 45676703,
        end: 45678037
      }, {
        filename: "/lib/python3.15/test/test_tools/__main__.py",
        start: 45678037,
        end: 45678109
      }, {
        filename: "/lib/python3.15/test/test_tools/i18n_data/ascii-escapes.pot",
        start: 45678109,
        end: 45679327
      }, {
        filename: "/lib/python3.15/test/test_tools/i18n_data/comments.pot",
        start: 45679327,
        end: 45681490
      }, {
        filename: "/lib/python3.15/test/test_tools/i18n_data/comments.py",
        start: 45681490,
        end: 45683068
      }, {
        filename: "/lib/python3.15/test/test_tools/i18n_data/custom_keywords.pot",
        start: 45683068,
        end: 45684042
      }, {
        filename: "/lib/python3.15/test/test_tools/i18n_data/custom_keywords.py",
        start: 45684042,
        end: 45684655
      }, {
        filename: "/lib/python3.15/test/test_tools/i18n_data/docstrings.pot",
        start: 45684655,
        end: 45685597
      }, {
        filename: "/lib/python3.15/test/test_tools/i18n_data/docstrings.py",
        start: 45685597,
        end: 45686267
      }, {
        filename: "/lib/python3.15/test/test_tools/i18n_data/escapes.pot",
        start: 45686267,
        end: 45687518
      }, {
        filename: "/lib/python3.15/test/test_tools/i18n_data/escapes.py",
        start: 45687518,
        end: 45688093
      }, {
        filename: "/lib/python3.15/test/test_tools/i18n_data/fileloc.pot",
        start: 45688093,
        end: 45688798
      }, {
        filename: "/lib/python3.15/test/test_tools/i18n_data/fileloc.py",
        start: 45688798,
        end: 45689147
      }, {
        filename: "/lib/python3.15/test/test_tools/i18n_data/messages.pot",
        start: 45689147,
        end: 45690826
      }, {
        filename: "/lib/python3.15/test/test_tools/i18n_data/messages.py",
        start: 45690826,
        end: 45692952
      }, {
        filename: "/lib/python3.15/test/test_tools/i18n_data/multiple_keywords.pot",
        start: 45692952,
        end: 45693708
      }, {
        filename: "/lib/python3.15/test/test_tools/i18n_data/multiple_keywords.py",
        start: 45693708,
        end: 45693941
      }, {
        filename: "/lib/python3.15/test/test_tools/msgfmt_data/fuzzy.json",
        start: 45693941,
        end: 45693944
      }, {
        filename: "/lib/python3.15/test/test_tools/msgfmt_data/fuzzy.mo",
        start: 45693944,
        end: 45693972
      }, {
        filename: "/lib/python3.15/test/test_tools/msgfmt_data/fuzzy.po",
        start: 45693972,
        end: 45694313
      }, {
        filename: "/lib/python3.15/test/test_tools/msgfmt_data/general.json",
        start: 45694313,
        end: 45695384
      }, {
        filename: "/lib/python3.15/test/test_tools/msgfmt_data/general.mo",
        start: 45695384,
        end: 45696055
      }, {
        filename: "/lib/python3.15/test/test_tools/msgfmt_data/general.po",
        start: 45696055,
        end: 45696925
      }, {
        filename: "/lib/python3.15/test/test_tools/test_freeze.py",
        start: 45696925,
        end: 45698294
      }, {
        filename: "/lib/python3.15/test/test_tools/test_i18n.py",
        start: 45698294,
        end: 45723188
      }, {
        filename: "/lib/python3.15/test/test_tools/test_makefile.py",
        start: 45723188,
        end: 45726058
      }, {
        filename: "/lib/python3.15/test/test_tools/test_makeunicodedata.py",
        start: 45726058,
        end: 45730012
      }, {
        filename: "/lib/python3.15/test/test_tools/test_msgfmt.py",
        start: 45730012,
        end: 45740631
      }, {
        filename: "/lib/python3.15/test/test_tools/test_reindent.py",
        start: 45740631,
        end: 45741670
      }, {
        filename: "/lib/python3.15/test/test_tools/test_sundry.py",
        start: 45741670,
        end: 45742580
      }, {
        filename: "/lib/python3.15/test/test_trace.py",
        start: 45742580,
        end: 45765050
      }, {
        filename: "/lib/python3.15/test/test_traceback.py",
        start: 45765050,
        end: 45970428
      }, {
        filename: "/lib/python3.15/test/test_tracemalloc.py",
        start: 45970428,
        end: 46012892
      }, {
        filename: "/lib/python3.15/test/test_tstring.py",
        start: 46012892,
        end: 46024043
      }, {
        filename: "/lib/python3.15/test/test_ttk/__init__.py",
        start: 46024043,
        end: 46025304
      }, {
        filename: "/lib/python3.15/test/test_ttk/__main__.py",
        start: 46025304,
        end: 46025362
      }, {
        filename: "/lib/python3.15/test/test_ttk/test_extensions.py",
        start: 46025362,
        end: 46037703
      }, {
        filename: "/lib/python3.15/test/test_ttk/test_style.py",
        start: 46037703,
        end: 46056343
      }, {
        filename: "/lib/python3.15/test/test_ttk/test_widgets.py",
        start: 46056343,
        end: 46130845
      }, {
        filename: "/lib/python3.15/test/test_ttk_textonly.py",
        start: 46130845,
        end: 46148714
      }, {
        filename: "/lib/python3.15/test/test_tty.py",
        start: 46148714,
        end: 46152431
      }, {
        filename: "/lib/python3.15/test/test_tuple.py",
        start: 46152431,
        end: 46173477
      }, {
        filename: "/lib/python3.15/test/test_turtle.py",
        start: 46173477,
        end: 46195922
      }, {
        filename: "/lib/python3.15/test/test_type_aliases.py",
        start: 46195922,
        end: 46213223
      }, {
        filename: "/lib/python3.15/test/test_type_annotations.py",
        start: 46213223,
        end: 46241845
      }, {
        filename: "/lib/python3.15/test/test_type_cache.py",
        start: 46241845,
        end: 46250067
      }, {
        filename: "/lib/python3.15/test/test_type_comments.py",
        start: 46250067,
        end: 46261332
      }, {
        filename: "/lib/python3.15/test/test_type_params.py",
        start: 46261332,
        end: 46309204
      }, {
        filename: "/lib/python3.15/test/test_typechecks.py",
        start: 46309204,
        end: 46311819
      }, {
        filename: "/lib/python3.15/test/test_types.py",
        start: 46311819,
        end: 46407651
      }, {
        filename: "/lib/python3.15/test/test_typing.py",
        start: 46407651,
        end: 46804806
      }, {
        filename: "/lib/python3.15/test/test_ucn.py",
        start: 46804806,
        end: 46814751
      }, {
        filename: "/lib/python3.15/test/test_unary.py",
        start: 46814751,
        end: 46816312
      }, {
        filename: "/lib/python3.15/test/test_unicode_file.py",
        start: 46816312,
        end: 46822168
      }, {
        filename: "/lib/python3.15/test/test_unicode_file_functions.py",
        start: 46822168,
        end: 46829206
      }, {
        filename: "/lib/python3.15/test/test_unicode_identifiers.py",
        start: 46829206,
        end: 46830217
      }, {
        filename: "/lib/python3.15/test/test_unicodedata.py",
        start: 46830217,
        end: 46866925
      }, {
        filename: "/lib/python3.15/test/test_unittest/__init__.py",
        start: 46866925,
        end: 46867073
      }, {
        filename: "/lib/python3.15/test/test_unittest/__main__.py",
        start: 46867073,
        end: 46867131
      }, {
        filename: "/lib/python3.15/test/test_unittest/_test_warnings.py",
        start: 46867131,
        end: 46869080
      }, {
        filename: "/lib/python3.15/test/test_unittest/dummy.py",
        start: 46869080,
        end: 46869130
      }, {
        filename: "/lib/python3.15/test/test_unittest/namespace_test_pkg/bar/__init__.py",
        start: 46869130,
        end: 46869130
      }, {
        filename: "/lib/python3.15/test/test_unittest/namespace_test_pkg/bar/test_bar.py",
        start: 46869130,
        end: 46869240
      }, {
        filename: "/lib/python3.15/test/test_unittest/namespace_test_pkg/noop/no2/__init__.py",
        start: 46869240,
        end: 46869240
      }, {
        filename: "/lib/python3.15/test/test_unittest/namespace_test_pkg/noop/no2/test_no2.py",
        start: 46869240,
        end: 46869350
      }, {
        filename: "/lib/python3.15/test/test_unittest/namespace_test_pkg/noop/test_noop.py",
        start: 46869350,
        end: 46869460
      }, {
        filename: "/lib/python3.15/test/test_unittest/namespace_test_pkg/test_foo.py",
        start: 46869460,
        end: 46869570
      }, {
        filename: "/lib/python3.15/test/test_unittest/support.py",
        start: 46869570,
        end: 46873608
      }, {
        filename: "/lib/python3.15/test/test_unittest/test_assertions.py",
        start: 46873608,
        end: 46890875
      }, {
        filename: "/lib/python3.15/test/test_unittest/test_async_case.py",
        start: 46890875,
        end: 46908331
      }, {
        filename: "/lib/python3.15/test/test_unittest/test_break.py",
        start: 46908331,
        end: 46919324
      }, {
        filename: "/lib/python3.15/test/test_unittest/test_case.py",
        start: 46919324,
        end: 47015897
      }, {
        filename: "/lib/python3.15/test/test_unittest/test_discovery.py",
        start: 47015897,
        end: 47051772
      }, {
        filename: "/lib/python3.15/test/test_unittest/test_functiontestcase.py",
        start: 47051772,
        end: 47057317
      }, {
        filename: "/lib/python3.15/test/test_unittest/test_loader.py",
        start: 47057317,
        end: 47116412
      }, {
        filename: "/lib/python3.15/test/test_unittest/test_program.py",
        start: 47116412,
        end: 47135290
      }, {
        filename: "/lib/python3.15/test/test_unittest/test_result.py",
        start: 47135290,
        end: 47190974
      }, {
        filename: "/lib/python3.15/test/test_unittest/test_runner.py",
        start: 47190974,
        end: 47245415
      }, {
        filename: "/lib/python3.15/test/test_unittest/test_setups.py",
        start: 47245415,
        end: 47261918
      }, {
        filename: "/lib/python3.15/test/test_unittest/test_skipping.py",
        start: 47261918,
        end: 47282098
      }, {
        filename: "/lib/python3.15/test/test_unittest/test_suite.py",
        start: 47282098,
        end: 47297287
      }, {
        filename: "/lib/python3.15/test/test_unittest/test_util.py",
        start: 47297287,
        end: 47298855
      }, {
        filename: "/lib/python3.15/test/test_unittest/testmock/__init__.py",
        start: 47298855,
        end: 47299003
      }, {
        filename: "/lib/python3.15/test/test_unittest/testmock/__main__.py",
        start: 47299003,
        end: 47299631
      }, {
        filename: "/lib/python3.15/test/test_unittest/testmock/support.py",
        start: 47299631,
        end: 47300097
      }, {
        filename: "/lib/python3.15/test/test_unittest/testmock/testasync.py",
        start: 47300097,
        end: 47339372
      }, {
        filename: "/lib/python3.15/test/test_unittest/testmock/testcallable.py",
        start: 47339372,
        end: 47343604
      }, {
        filename: "/lib/python3.15/test/test_unittest/testmock/testhelpers.py",
        start: 47343604,
        end: 47381821
      }, {
        filename: "/lib/python3.15/test/test_unittest/testmock/testmagicmethods.py",
        start: 47381821,
        end: 47399518
      }, {
        filename: "/lib/python3.15/test/test_unittest/testmock/testmock.py",
        start: 47399518,
        end: 47482379
      }, {
        filename: "/lib/python3.15/test/test_unittest/testmock/testpatch.py",
        start: 47482379,
        end: 47547623
      }, {
        filename: "/lib/python3.15/test/test_unittest/testmock/testsealable.py",
        start: 47547623,
        end: 47555028
      }, {
        filename: "/lib/python3.15/test/test_unittest/testmock/testsentinel.py",
        start: 47555028,
        end: 47556353
      }, {
        filename: "/lib/python3.15/test/test_unittest/testmock/testthreadingmock.py",
        start: 47556353,
        end: 47566991
      }, {
        filename: "/lib/python3.15/test/test_unittest/testmock/testwith.py",
        start: 47566991,
        end: 47579273
      }, {
        filename: "/lib/python3.15/test/test_unpack.py",
        start: 47579273,
        end: 47584234
      }, {
        filename: "/lib/python3.15/test/test_unpack_ex.py",
        start: 47584234,
        end: 47594450
      }, {
        filename: "/lib/python3.15/test/test_unparse.py",
        start: 47594450,
        end: 47633644
      }, {
        filename: "/lib/python3.15/test/test_urllib.py",
        start: 47633644,
        end: 47707106
      }, {
        filename: "/lib/python3.15/test/test_urllib2.py",
        start: 47707106,
        end: 47792504
      }, {
        filename: "/lib/python3.15/test/test_urllib2_localnet.py",
        start: 47792504,
        end: 47817243
      }, {
        filename: "/lib/python3.15/test/test_urllib2net.py",
        start: 47817243,
        end: 47832446
      }, {
        filename: "/lib/python3.15/test/test_urllib_response.py",
        start: 47832446,
        end: 47834535
      }, {
        filename: "/lib/python3.15/test/test_urllibnet.py",
        start: 47834535,
        end: 47844031
      }, {
        filename: "/lib/python3.15/test/test_urlparse.py",
        start: 47844031,
        end: 47933150
      }, {
        filename: "/lib/python3.15/test/test_userdict.py",
        start: 47933150,
        end: 47940957
      }, {
        filename: "/lib/python3.15/test/test_userlist.py",
        start: 47940957,
        end: 47943165
      }, {
        filename: "/lib/python3.15/test/test_userstring.py",
        start: 47943165,
        end: 47945700
      }, {
        filename: "/lib/python3.15/test/test_utf8_mode.py",
        start: 47945700,
        end: 47956256
      }, {
        filename: "/lib/python3.15/test/test_utf8source.py",
        start: 47956256,
        end: 47957377
      }, {
        filename: "/lib/python3.15/test/test_uuid.py",
        start: 47957377,
        end: 48024436
      }, {
        filename: "/lib/python3.15/test/test_venv.py",
        start: 48024436,
        end: 48068947
      }, {
        filename: "/lib/python3.15/test/test_wait3.py",
        start: 48068947,
        end: 48070728
      }, {
        filename: "/lib/python3.15/test/test_wait4.py",
        start: 48070728,
        end: 48071895
      }, {
        filename: "/lib/python3.15/test/test_warnings/__init__.py",
        start: 48071895,
        end: 48161575
      }, {
        filename: "/lib/python3.15/test/test_warnings/__main__.py",
        start: 48161575,
        end: 48161628
      }, {
        filename: "/lib/python3.15/test/test_warnings/data/import_warning.py",
        start: 48161628,
        end: 48161717
      }, {
        filename: "/lib/python3.15/test/test_warnings/data/package_helper.py",
        start: 48161717,
        end: 48162e3
      }, {
        filename: "/lib/python3.15/test/test_warnings/data/stacklevel.py",
        start: 48162e3,
        end: 48162590
      }, {
        filename: "/lib/python3.15/test/test_wave.py",
        start: 48162590,
        end: 48171556
      }, {
        filename: "/lib/python3.15/test/test_weakref.py",
        start: 48171556,
        end: 48252448
      }, {
        filename: "/lib/python3.15/test/test_weakset.py",
        start: 48252448,
        end: 48269109
      }, {
        filename: "/lib/python3.15/test/test_webbrowser.py",
        start: 48269109,
        end: 48289302
      }, {
        filename: "/lib/python3.15/test/test_winapi.py",
        start: 48289302,
        end: 48295194
      }, {
        filename: "/lib/python3.15/test/test_winconsoleio.py",
        start: 48295194,
        end: 48303433
      }, {
        filename: "/lib/python3.15/test/test_winreg.py",
        start: 48303433,
        end: 48329250
      }, {
        filename: "/lib/python3.15/test/test_winsound.py",
        start: 48329250,
        end: 48335195
      }, {
        filename: "/lib/python3.15/test/test_with.py",
        start: 48335195,
        end: 48365661
      }, {
        filename: "/lib/python3.15/test/test_wmi.py",
        start: 48365661,
        end: 48369027
      }, {
        filename: "/lib/python3.15/test/test_wsgiref.py",
        start: 48369027,
        end: 48399405
      }, {
        filename: "/lib/python3.15/test/test_xml_dom_minicompat.py",
        start: 48399405,
        end: 48403687
      }, {
        filename: "/lib/python3.15/test/test_xml_dom_xmlbuilder.py",
        start: 48403687,
        end: 48406859
      }, {
        filename: "/lib/python3.15/test/test_xml_etree.py",
        start: 48406859,
        end: 48587934
      }, {
        filename: "/lib/python3.15/test/test_xml_etree_c.py",
        start: 48587934,
        end: 48597581
      }, {
        filename: "/lib/python3.15/test/test_xmlrpc.py",
        start: 48597581,
        end: 48657312
      }, {
        filename: "/lib/python3.15/test/test_xxlimited.py",
        start: 48657312,
        end: 48659827
      }, {
        filename: "/lib/python3.15/test/test_xxtestfuzz.py",
        start: 48659827,
        end: 48660517
      }, {
        filename: "/lib/python3.15/test/test_yield_from.py",
        start: 48660517,
        end: 48712557
      }, {
        filename: "/lib/python3.15/test/test_zipapp.py",
        start: 48712557,
        end: 48731117
      }, {
        filename: "/lib/python3.15/test/test_zipfile/__init__.py",
        start: 48731117,
        end: 48731259
      }, {
        filename: "/lib/python3.15/test/test_zipfile/__main__.py",
        start: 48731259,
        end: 48731350
      }, {
        filename: "/lib/python3.15/test/test_zipfile/_path/__init__.py",
        start: 48731350,
        end: 48731350
      }, {
        filename: "/lib/python3.15/test/test_zipfile/_path/_functools.py",
        start: 48731350,
        end: 48731561
      }, {
        filename: "/lib/python3.15/test/test_zipfile/_path/_itertools.py",
        start: 48731561,
        end: 48733651
      }, {
        filename: "/lib/python3.15/test/test_zipfile/_path/_support.py",
        start: 48733651,
        end: 48733870
      }, {
        filename: "/lib/python3.15/test/test_zipfile/_path/_test_params.py",
        start: 48733870,
        end: 48734775
      }, {
        filename: "/lib/python3.15/test/test_zipfile/_path/test_complexity.py",
        start: 48734775,
        end: 48738037
      }, {
        filename: "/lib/python3.15/test/test_zipfile/_path/test_path.py",
        start: 48738037,
        end: 48760144
      }, {
        filename: "/lib/python3.15/test/test_zipfile/_path/write-alpharep.py",
        start: 48760144,
        end: 48760254
      }, {
        filename: "/lib/python3.15/test/test_zipfile/test_core.py",
        start: 48760254,
        end: 48925520
      }, {
        filename: "/lib/python3.15/test/test_zipfile64.py",
        start: 48925520,
        end: 48931443
      }, {
        filename: "/lib/python3.15/test/test_zipimport.py",
        start: 48931443,
        end: 48976468
      }, {
        filename: "/lib/python3.15/test/test_zipimport_support.py",
        start: 48976468,
        end: 48988491
      }, {
        filename: "/lib/python3.15/test/test_zlib.py",
        start: 48988491,
        end: 49035105
      }, {
        filename: "/lib/python3.15/test/test_zoneinfo/__init__.py",
        start: 49035105,
        end: 49035247
      }, {
        filename: "/lib/python3.15/test/test_zoneinfo/__main__.py",
        start: 49035247,
        end: 49035300
      }, {
        filename: "/lib/python3.15/test/test_zoneinfo/_support.py",
        start: 49035300,
        end: 49038500
      }, {
        filename: "/lib/python3.15/test/test_zoneinfo/data/update_test_data.py",
        start: 49038500,
        end: 49041772
      }, {
        filename: "/lib/python3.15/test/test_zoneinfo/data/zoneinfo_data.json",
        start: 49041772,
        end: 49054952
      }, {
        filename: "/lib/python3.15/test/test_zoneinfo/test_zoneinfo.py",
        start: 49054952,
        end: 49138732
      }, {
        filename: "/lib/python3.15/test/test_zoneinfo/test_zoneinfo_property.py",
        start: 49138732,
        end: 49150915
      }, {
        filename: "/lib/python3.15/test/test_zstd.py",
        start: 49150915,
        end: 49250656
      }, {
        filename: "/lib/python3.15/test/testcodec.py",
        start: 49250656,
        end: 49251702
      }, {
        filename: "/lib/python3.15/test/tf_inherit_check.py",
        start: 49251702,
        end: 49252416
      }, {
        filename: "/lib/python3.15/test/tkinterdata/python.gif",
        start: 49252416,
        end: 49252821
      }, {
        filename: "/lib/python3.15/test/tkinterdata/python.pgm",
        start: 49252821,
        end: 49253090
      }, {
        filename: "/lib/python3.15/test/tkinterdata/python.png",
        start: 49253090,
        end: 49254110
      }, {
        filename: "/lib/python3.15/test/tkinterdata/python.ppm",
        start: 49254110,
        end: 49254891
      }, {
        filename: "/lib/python3.15/test/tkinterdata/python.xbm",
        start: 49254891,
        end: 49255173
      }, {
        filename: "/lib/python3.15/test/tokenizedata/__init__.py",
        start: 49255173,
        end: 49255173
      }, {
        filename: "/lib/python3.15/test/tokenizedata/bad_coding.py",
        start: 49255173,
        end: 49255197
      }, {
        filename: "/lib/python3.15/test/tokenizedata/bad_coding2.py",
        start: 49255197,
        end: 49255227
      }, {
        filename: "/lib/python3.15/test/tokenizedata/badsyntax_3131.py",
        start: 49255227,
        end: 49255259
      }, {
        filename: "/lib/python3.15/test/tokenizedata/badsyntax_pep3120.py",
        start: 49255259,
        end: 49255273
      }, {
        filename: "/lib/python3.15/test/tokenizedata/coding20731.py",
        start: 49255273,
        end: 49255295
      }, {
        filename: "/lib/python3.15/test/tokenizedata/tokenize_tests-latin1-coding-cookie-and-utf8-bom-sig.txt",
        start: 49255295,
        end: 49255738
      }, {
        filename: "/lib/python3.15/test/tokenizedata/tokenize_tests-no-coding-cookie-and-utf8-bom-sig-only.txt",
        start: 49255738,
        end: 49256040
      }, {
        filename: "/lib/python3.15/test/tokenizedata/tokenize_tests-utf8-coding-cookie-and-no-utf8-bom-sig.txt",
        start: 49256040,
        end: 49256461
      }, {
        filename: "/lib/python3.15/test/tokenizedata/tokenize_tests-utf8-coding-cookie-and-utf8-bom-sig.txt",
        start: 49256461,
        end: 49256787
      }, {
        filename: "/lib/python3.15/test/tokenizedata/tokenize_tests.txt",
        start: 49256787,
        end: 49259504
      }, {
        filename: "/lib/python3.15/test/tracedmodules/__init__.py",
        start: 49259504,
        end: 49259707
      }, {
        filename: "/lib/python3.15/test/tracedmodules/testmod.py",
        start: 49259707,
        end: 49259850
      }, {
        filename: "/lib/python3.15/test/translationdata/argparse/msgids.txt",
        start: 49259850,
        end: 49260890
      }, {
        filename: "/lib/python3.15/test/translationdata/getopt/msgids.txt",
        start: 49260890,
        end: 49261093
      }, {
        filename: "/lib/python3.15/test/translationdata/optparse/msgids.txt",
        start: 49261093,
        end: 49261440
      }, {
        filename: "/lib/python3.15/test/typinganndata/__init__.py",
        start: 49261440,
        end: 49261440
      }, {
        filename: "/lib/python3.15/test/typinganndata/_typed_dict_helper.py",
        start: 49261440,
        end: 49262299
      }, {
        filename: "/lib/python3.15/test/typinganndata/ann_module.py",
        start: 49262299,
        end: 49263361
      }, {
        filename: "/lib/python3.15/test/typinganndata/ann_module2.py",
        start: 49263361,
        end: 49263880
      }, {
        filename: "/lib/python3.15/test/typinganndata/ann_module3.py",
        start: 49263880,
        end: 49264328
      }, {
        filename: "/lib/python3.15/test/typinganndata/ann_module4.py",
        start: 49264328,
        end: 49264409
      }, {
        filename: "/lib/python3.15/test/typinganndata/ann_module5.py",
        start: 49264409,
        end: 49264611
      }, {
        filename: "/lib/python3.15/test/typinganndata/ann_module6.py",
        start: 49264611,
        end: 49264749
      }, {
        filename: "/lib/python3.15/test/typinganndata/ann_module695.py",
        start: 49264749,
        end: 49265983
      }, {
        filename: "/lib/python3.15/test/typinganndata/ann_module7.py",
        start: 49265983,
        end: 49266278
      }, {
        filename: "/lib/python3.15/test/typinganndata/ann_module8.py",
        start: 49266278,
        end: 49266455
      }, {
        filename: "/lib/python3.15/test/typinganndata/ann_module9.py",
        start: 49266455,
        end: 49266735
      }, {
        filename: "/lib/python3.15/test/typinganndata/fwdref_module.py",
        start: 49266735,
        end: 49266858
      }, {
        filename: "/lib/python3.15/test/typinganndata/mod_generics_cache.py",
        start: 49266858,
        end: 49267366
      }, {
        filename: "/lib/python3.15/test/typinganndata/partialexecution/__init__.py",
        start: 49267366,
        end: 49267382
      }, {
        filename: "/lib/python3.15/test/typinganndata/partialexecution/a.py",
        start: 49267382,
        end: 49267416
      }, {
        filename: "/lib/python3.15/test/typinganndata/partialexecution/b.py",
        start: 49267416,
        end: 49267459
      }, {
        filename: "/lib/python3.15/test/wheeldata/setuptools-79.0.1-py3-none-any.whl",
        start: 49267459,
        end: 50523740
      }, {
        filename: "/lib/python3.15/test/win_console_handler.py",
        start: 50523740,
        end: 50525156
      }, {
        filename: "/lib/python3.15/test/xmltestdata/c14n-20/README",
        start: 50525156,
        end: 50527022
      }, {
        filename: "/lib/python3.15/test/xmltestdata/c14n-20/c14nComment.xml",
        start: 50527022,
        end: 50527275
      }, {
        filename: "/lib/python3.15/test/xmltestdata/c14n-20/c14nDefault.xml",
        start: 50527275,
        end: 50527430
      }, {
        filename: "/lib/python3.15/test/xmltestdata/c14n-20/c14nPrefix.xml",
        start: 50527430,
        end: 50527687
      }, {
        filename: "/lib/python3.15/test/xmltestdata/c14n-20/c14nPrefixQname.xml",
        start: 50527687,
        end: 50528073
      }, {
        filename: "/lib/python3.15/test/xmltestdata/c14n-20/c14nPrefixQnameXpathElem.xml",
        start: 50528073,
        end: 50528503
      }, {
        filename: "/lib/python3.15/test/xmltestdata/c14n-20/c14nQname.xml",
        start: 50528503,
        end: 50528833
      }, {
        filename: "/lib/python3.15/test/xmltestdata/c14n-20/c14nQnameElem.xml",
        start: 50528833,
        end: 50529123
      }, {
        filename: "/lib/python3.15/test/xmltestdata/c14n-20/c14nQnameXpathElem.xml",
        start: 50529123,
        end: 50529497
      }, {
        filename: "/lib/python3.15/test/xmltestdata/c14n-20/c14nTrim.xml",
        start: 50529497,
        end: 50529748
      }, {
        filename: "/lib/python3.15/test/xmltestdata/c14n-20/doc.dtd",
        start: 50529748,
        end: 50529816
      }, {
        filename: "/lib/python3.15/test/xmltestdata/c14n-20/doc.xsl",
        start: 50529816,
        end: 50529969
      }, {
        filename: "/lib/python3.15/test/xmltestdata/c14n-20/inC14N1.xml",
        start: 50529969,
        end: 50530193
      }, {
        filename: "/lib/python3.15/test/xmltestdata/c14n-20/inC14N2.xml",
        start: 50530193,
        end: 50530363
      }, {
        filename: "/lib/python3.15/test/xmltestdata/c14n-20/inC14N3.xml",
        start: 50530363,
        end: 50530935
      }, {
        filename: "/lib/python3.15/test/xmltestdata/c14n-20/inC14N4.xml",
        start: 50530935,
        end: 50531451
      }, {
        filename: "/lib/python3.15/test/xmltestdata/c14n-20/inC14N5.xml",
        start: 50531451,
        end: 50531766
      }, {
        filename: "/lib/python3.15/test/xmltestdata/c14n-20/inC14N6.xml",
        start: 50531766,
        end: 50531828
      }, {
        filename: "/lib/python3.15/test/xmltestdata/c14n-20/inNsContent.xml",
        start: 50531828,
        end: 50532196
      }, {
        filename: "/lib/python3.15/test/xmltestdata/c14n-20/inNsDefault.xml",
        start: 50532196,
        end: 50532281
      }, {
        filename: "/lib/python3.15/test/xmltestdata/c14n-20/inNsPushdown.xml",
        start: 50532281,
        end: 50532408
      }, {
        filename: "/lib/python3.15/test/xmltestdata/c14n-20/inNsRedecl.xml",
        start: 50532408,
        end: 50532585
      }, {
        filename: "/lib/python3.15/test/xmltestdata/c14n-20/inNsSort.xml",
        start: 50532585,
        end: 50532758
      }, {
        filename: "/lib/python3.15/test/xmltestdata/c14n-20/inNsSuperfluous.xml",
        start: 50532758,
        end: 50532952
      }, {
        filename: "/lib/python3.15/test/xmltestdata/c14n-20/inNsXml.xml",
        start: 50532952,
        end: 50533134
      }, {
        filename: "/lib/python3.15/test/xmltestdata/c14n-20/out_inC14N1_c14nComment.xml",
        start: 50533134,
        end: 50533290
      }, {
        filename: "/lib/python3.15/test/xmltestdata/c14n-20/out_inC14N1_c14nDefault.xml",
        start: 50533290,
        end: 50533390
      }, {
        filename: "/lib/python3.15/test/xmltestdata/c14n-20/out_inC14N2_c14nDefault.xml",
        start: 50533390,
        end: 50533559
      }, {
        filename: "/lib/python3.15/test/xmltestdata/c14n-20/out_inC14N2_c14nTrim.xml",
        start: 50533559,
        end: 50533658
      }, {
        filename: "/lib/python3.15/test/xmltestdata/c14n-20/out_inC14N3_c14nDefault.xml",
        start: 50533658,
        end: 50534063
      }, {
        filename: "/lib/python3.15/test/xmltestdata/c14n-20/out_inC14N3_c14nPrefix.xml",
        start: 50534063,
        end: 50534541
      }, {
        filename: "/lib/python3.15/test/xmltestdata/c14n-20/out_inC14N3_c14nTrim.xml",
        start: 50534541,
        end: 50534870
      }, {
        filename: "/lib/python3.15/test/xmltestdata/c14n-20/out_inC14N4_c14nDefault.xml",
        start: 50534870,
        end: 50535301
      }, {
        filename: "/lib/python3.15/test/xmltestdata/c14n-20/out_inC14N4_c14nTrim.xml",
        start: 50535301,
        end: 50535703
      }, {
        filename: "/lib/python3.15/test/xmltestdata/c14n-20/out_inC14N5_c14nDefault.xml",
        start: 50535703,
        end: 50535752
      }, {
        filename: "/lib/python3.15/test/xmltestdata/c14n-20/out_inC14N5_c14nTrim.xml",
        start: 50535752,
        end: 50535796
      }, {
        filename: "/lib/python3.15/test/xmltestdata/c14n-20/out_inC14N6_c14nDefault.xml",
        start: 50535796,
        end: 50535809
      }, {
        filename: "/lib/python3.15/test/xmltestdata/c14n-20/out_inNsContent_c14nDefault.xml",
        start: 50535809,
        end: 50536034
      }, {
        filename: "/lib/python3.15/test/xmltestdata/c14n-20/out_inNsContent_c14nPrefixQnameXpathElem.xml",
        start: 50536034,
        end: 50536362
      }, {
        filename: "/lib/python3.15/test/xmltestdata/c14n-20/out_inNsContent_c14nQnameElem.xml",
        start: 50536362,
        end: 50536632
      }, {
        filename: "/lib/python3.15/test/xmltestdata/c14n-20/out_inNsContent_c14nQnameXpathElem.xml",
        start: 50536632,
        end: 50536976
      }, {
        filename: "/lib/python3.15/test/xmltestdata/c14n-20/out_inNsDefault_c14nDefault.xml",
        start: 50536976,
        end: 50537048
      }, {
        filename: "/lib/python3.15/test/xmltestdata/c14n-20/out_inNsDefault_c14nPrefix.xml",
        start: 50537048,
        end: 50537142
      }, {
        filename: "/lib/python3.15/test/xmltestdata/c14n-20/out_inNsPushdown_c14nDefault.xml",
        start: 50537142,
        end: 50537334
      }, {
        filename: "/lib/python3.15/test/xmltestdata/c14n-20/out_inNsPushdown_c14nPrefix.xml",
        start: 50537334,
        end: 50537542
      }, {
        filename: "/lib/python3.15/test/xmltestdata/c14n-20/out_inNsRedecl_c14nDefault.xml",
        start: 50537542,
        end: 50537722
      }, {
        filename: "/lib/python3.15/test/xmltestdata/c14n-20/out_inNsRedecl_c14nPrefix.xml",
        start: 50537722,
        end: 50537895
      }, {
        filename: "/lib/python3.15/test/xmltestdata/c14n-20/out_inNsSort_c14nDefault.xml",
        start: 50537895,
        end: 50538081
      }, {
        filename: "/lib/python3.15/test/xmltestdata/c14n-20/out_inNsSort_c14nPrefix.xml",
        start: 50538081,
        end: 50538281
      }, {
        filename: "/lib/python3.15/test/xmltestdata/c14n-20/out_inNsSuperfluous_c14nDefault.xml",
        start: 50538281,
        end: 50538468
      }, {
        filename: "/lib/python3.15/test/xmltestdata/c14n-20/out_inNsSuperfluous_c14nPrefix.xml",
        start: 50538468,
        end: 50538591
      }, {
        filename: "/lib/python3.15/test/xmltestdata/c14n-20/out_inNsXml_c14nDefault.xml",
        start: 50538591,
        end: 50538727
      }, {
        filename: "/lib/python3.15/test/xmltestdata/c14n-20/out_inNsXml_c14nPrefix.xml",
        start: 50538727,
        end: 50538876
      }, {
        filename: "/lib/python3.15/test/xmltestdata/c14n-20/out_inNsXml_c14nPrefixQname.xml",
        start: 50538876,
        end: 50539068
      }, {
        filename: "/lib/python3.15/test/xmltestdata/c14n-20/out_inNsXml_c14nQname.xml",
        start: 50539068,
        end: 50539249
      }, {
        filename: "/lib/python3.15/test/xmltestdata/c14n-20/world.txt",
        start: 50539249,
        end: 50539254
      }, {
        filename: "/lib/python3.15/test/xmltestdata/expat224_utf8_bug.xml",
        start: 50539254,
        end: 50540290
      }, {
        filename: "/lib/python3.15/test/xmltestdata/simple-ns.xml",
        start: 50540290,
        end: 50540442
      }, {
        filename: "/lib/python3.15/test/xmltestdata/simple.xml",
        start: 50540442,
        end: 50540564
      }, {
        filename: "/lib/python3.15/test/xmltestdata/test.xml",
        start: 50540564,
        end: 50541952
      }, {
        filename: "/lib/python3.15/test/xmltestdata/test.xml.out",
        start: 50541952,
        end: 50543339
      }, {
        filename: "/lib/python3.15/test/xmltests.py",
        start: 50543339,
        end: 50543838
      }, {
        filename: "/lib/python3.15/test/zipimport_data/sparse-zip64-c0-0x000000000.part",
        start: 50543838,
        end: 50547934
      }, {
        filename: "/lib/python3.15/test/zipimport_data/sparse-zip64-c0-0x100000000.part",
        start: 50547934,
        end: 50552030
      }, {
        filename: "/lib/python3.15/test/zipimport_data/sparse-zip64-c0-0x200000000.part",
        start: 50552030,
        end: 50552576
      }, {
        filename: "/lib/python3.15/textwrap.py",
        start: 50552576,
        end: 50571958
      }, {
        filename: "/lib/python3.15/this.py",
        start: 50571958,
        end: 50572961
      }, {
        filename: "/lib/python3.15/threading.py",
        start: 50572961,
        end: 50629695
      }, {
        filename: "/lib/python3.15/timeit.py",
        start: 50629695,
        end: 50643560
      }, {
        filename: "/lib/python3.15/tkinter/__init__.py",
        start: 50643560,
        end: 50833094
      }, {
        filename: "/lib/python3.15/tkinter/__main__.py",
        start: 50833094,
        end: 50833242
      }, {
        filename: "/lib/python3.15/tkinter/colorchooser.py",
        start: 50833242,
        end: 50835902
      }, {
        filename: "/lib/python3.15/tkinter/commondialog.py",
        start: 50835902,
        end: 50837191
      }, {
        filename: "/lib/python3.15/tkinter/constants.py",
        start: 50837191,
        end: 50838684
      }, {
        filename: "/lib/python3.15/tkinter/dialog.py",
        start: 50838684,
        end: 50840219
      }, {
        filename: "/lib/python3.15/tkinter/dnd.py",
        start: 50840219,
        end: 50851863
      }, {
        filename: "/lib/python3.15/tkinter/filedialog.py",
        start: 50851863,
        end: 50866802
      }, {
        filename: "/lib/python3.15/tkinter/font.py",
        start: 50866802,
        end: 50874107
      }, {
        filename: "/lib/python3.15/tkinter/messagebox.py",
        start: 50874107,
        end: 50877968
      }, {
        filename: "/lib/python3.15/tkinter/scrolledtext.py",
        start: 50877968,
        end: 50879776
      }, {
        filename: "/lib/python3.15/tkinter/simpledialog.py",
        start: 50879776,
        end: 50891718
      }, {
        filename: "/lib/python3.15/tkinter/ttk.py",
        start: 50891718,
        end: 50948552
      }, {
        filename: "/lib/python3.15/token.py",
        start: 50948552,
        end: 50951136
      }, {
        filename: "/lib/python3.15/tokenize.py",
        start: 50951136,
        end: 50972977
      }, {
        filename: "/lib/python3.15/tomllib/__init__.py",
        start: 50972977,
        end: 50973285
      }, {
        filename: "/lib/python3.15/tomllib/_parser.py",
        start: 50973285,
        end: 50997871
      }, {
        filename: "/lib/python3.15/tomllib/_re.py",
        start: 50997871,
        end: 51001063
      }, {
        filename: "/lib/python3.15/tomllib/_types.py",
        start: 51001063,
        end: 51001317
      }, {
        filename: "/lib/python3.15/tomllib/mypy.ini",
        start: 51001317,
        end: 51001768
      }, {
        filename: "/lib/python3.15/trace.py",
        start: 51001768,
        end: 51031373
      }, {
        filename: "/lib/python3.15/traceback.py",
        start: 51031373,
        end: 51105068
      }, {
        filename: "/lib/python3.15/tracemalloc.py",
        start: 51105068,
        end: 51123115
      }, {
        filename: "/lib/python3.15/tty.py",
        start: 51123115,
        end: 51125150
      }, {
        filename: "/lib/python3.15/turtle.py",
        start: 51125150,
        end: 51274655
      }, {
        filename: "/lib/python3.15/turtledemo/__init__.py",
        start: 51274655,
        end: 51274969
      }, {
        filename: "/lib/python3.15/turtledemo/__main__.py",
        start: 51274969,
        end: 51290300
      }, {
        filename: "/lib/python3.15/turtledemo/bytedesign.py",
        start: 51290300,
        end: 51294493
      }, {
        filename: "/lib/python3.15/turtledemo/chaos.py",
        start: 51294493,
        end: 51295404
      }, {
        filename: "/lib/python3.15/turtledemo/clock.py",
        start: 51295404,
        end: 51298532
      }, {
        filename: "/lib/python3.15/turtledemo/colormixer.py",
        start: 51298532,
        end: 51299888
      }, {
        filename: "/lib/python3.15/turtledemo/forest.py",
        start: 51299888,
        end: 51302734
      }, {
        filename: "/lib/python3.15/turtledemo/fractalcurves.py",
        start: 51302734,
        end: 51306152
      }, {
        filename: "/lib/python3.15/turtledemo/lindenmayer.py",
        start: 51306152,
        end: 51308525
      }, {
        filename: "/lib/python3.15/turtledemo/minimal_hanoi.py",
        start: 51308525,
        end: 51310404
      }, {
        filename: "/lib/python3.15/turtledemo/nim.py",
        start: 51310404,
        end: 51316881
      }, {
        filename: "/lib/python3.15/turtledemo/paint.py",
        start: 51316881,
        end: 51318033
      }, {
        filename: "/lib/python3.15/turtledemo/peace.py",
        start: 51318033,
        end: 51319037
      }, {
        filename: "/lib/python3.15/turtledemo/penrose.py",
        start: 51319037,
        end: 51322353
      }, {
        filename: "/lib/python3.15/turtledemo/planet_and_moon.py",
        start: 51322353,
        end: 51325122
      }, {
        filename: "/lib/python3.15/turtledemo/rosette.py",
        start: 51325122,
        end: 51326446
      }, {
        filename: "/lib/python3.15/turtledemo/round_dance.py",
        start: 51326446,
        end: 51328148
      }, {
        filename: "/lib/python3.15/turtledemo/sorting_animate.py",
        start: 51328148,
        end: 51333062
      }, {
        filename: "/lib/python3.15/turtledemo/tree.py",
        start: 51333062,
        end: 51334403
      }, {
        filename: "/lib/python3.15/turtledemo/turtle.cfg",
        start: 51334403,
        end: 51334563
      }, {
        filename: "/lib/python3.15/turtledemo/two_canvases.py",
        start: 51334563,
        end: 51335685
      }, {
        filename: "/lib/python3.15/turtledemo/yinyang.py",
        start: 51335685,
        end: 51336446
      }, {
        filename: "/lib/python3.15/types.py",
        start: 51336446,
        end: 51347769
      }, {
        filename: "/lib/python3.15/typing.py",
        start: 51347769,
        end: 51483926
      }, {
        filename: "/lib/python3.15/unittest/__init__.py",
        start: 51483926,
        end: 51487172
      }, {
        filename: "/lib/python3.15/unittest/__main__.py",
        start: 51487172,
        end: 51487644
      }, {
        filename: "/lib/python3.15/unittest/_log.py",
        start: 51487644,
        end: 51490459
      }, {
        filename: "/lib/python3.15/unittest/async_case.py",
        start: 51490459,
        end: 51496466
      }, {
        filename: "/lib/python3.15/unittest/case.py",
        start: 51496466,
        end: 51560717
      }, {
        filename: "/lib/python3.15/unittest/loader.py",
        start: 51560717,
        end: 51581537
      }, {
        filename: "/lib/python3.15/unittest/main.py",
        start: 51581537,
        end: 51593197
      }, {
        filename: "/lib/python3.15/unittest/mock.py",
        start: 51593197,
        end: 51704948
      }, {
        filename: "/lib/python3.15/unittest/result.py",
        start: 51704948,
        end: 51714217
      }, {
        filename: "/lib/python3.15/unittest/runner.py",
        start: 51714217,
        end: 51725600
      }, {
        filename: "/lib/python3.15/unittest/signals.py",
        start: 51725600,
        end: 51728003
      }, {
        filename: "/lib/python3.15/unittest/suite.py",
        start: 51728003,
        end: 51742245
      }, {
        filename: "/lib/python3.15/unittest/util.py",
        start: 51742245,
        end: 51747460
      }, {
        filename: "/lib/python3.15/urllib/__init__.py",
        start: 51747460,
        end: 51747460
      }, {
        filename: "/lib/python3.15/urllib/error.py",
        start: 51747460,
        end: 51749870
      }, {
        filename: "/lib/python3.15/urllib/parse.py",
        start: 51749870,
        end: 51796650
      }, {
        filename: "/lib/python3.15/urllib/request.py",
        start: 51796650,
        end: 51873525
      }, {
        filename: "/lib/python3.15/urllib/response.py",
        start: 51873525,
        end: 51875886
      }, {
        filename: "/lib/python3.15/urllib/robotparser.py",
        start: 51875886,
        end: 51885739
      }, {
        filename: "/lib/python3.15/uuid.py",
        start: 51885739,
        end: 51923934
      }, {
        filename: "/lib/python3.15/venv/__init__.py",
        start: 51923934,
        end: 51954934
      }, {
        filename: "/lib/python3.15/venv/__main__.py",
        start: 51954934,
        end: 51955075
      }, {
        filename: "/lib/python3.15/venv/scripts/common/Activate.ps1",
        start: 51955075,
        end: 51964106
      }, {
        filename: "/lib/python3.15/venv/scripts/common/activate",
        start: 51964106,
        end: 51966276
      }, {
        filename: "/lib/python3.15/venv/scripts/common/activate.fish",
        start: 51966276,
        end: 51968484
      }, {
        filename: "/lib/python3.15/venv/scripts/nt/activate.bat",
        start: 51968484,
        end: 51969504
      }, {
        filename: "/lib/python3.15/venv/scripts/nt/deactivate.bat",
        start: 51969504,
        end: 51969897
      }, {
        filename: "/lib/python3.15/venv/scripts/posix/activate.csh",
        start: 51969897,
        end: 51970834
      }, {
        filename: "/lib/python3.15/warnings.py",
        start: 51970834,
        end: 51972800
      }, {
        filename: "/lib/python3.15/wave.py",
        start: 51972800,
        end: 51995106
      }, {
        filename: "/lib/python3.15/weakref.py",
        start: 51995106,
        end: 52012877
      }, {
        filename: "/lib/python3.15/webbrowser.py",
        start: 52012877,
        end: 52039007
      }, {
        filename: "/lib/python3.15/wsgiref/__init__.py",
        start: 52039007,
        end: 52039664
      }, {
        filename: "/lib/python3.15/wsgiref/handlers.py",
        start: 52039664,
        end: 52061421
      }, {
        filename: "/lib/python3.15/wsgiref/headers.py",
        start: 52061421,
        end: 52068182
      }, {
        filename: "/lib/python3.15/wsgiref/simple_server.py",
        start: 52068182,
        end: 52073445
      }, {
        filename: "/lib/python3.15/wsgiref/types.py",
        start: 52073445,
        end: 52075162
      }, {
        filename: "/lib/python3.15/wsgiref/util.py",
        start: 52075162,
        end: 52080651
      }, {
        filename: "/lib/python3.15/wsgiref/validate.py",
        start: 52080651,
        end: 52095687
      }, {
        filename: "/lib/python3.15/xml/__init__.py",
        start: 52095687,
        end: 52096244
      }, {
        filename: "/lib/python3.15/xml/__pycache__/__init__.cpython-315.pyc",
        start: 52096244,
        end: 52096951
      }, {
        filename: "/lib/python3.15/xml/dom/NodeFilter.py",
        start: 52096951,
        end: 52097887
      }, {
        filename: "/lib/python3.15/xml/dom/__init__.py",
        start: 52097887,
        end: 52101920
      }, {
        filename: "/lib/python3.15/xml/dom/domreg.py",
        start: 52101920,
        end: 52105371
      }, {
        filename: "/lib/python3.15/xml/dom/expatbuilder.py",
        start: 52105371,
        end: 52141064
      }, {
        filename: "/lib/python3.15/xml/dom/minicompat.py",
        start: 52141064,
        end: 52144431
      }, {
        filename: "/lib/python3.15/xml/dom/minidom.py",
        start: 52144431,
        end: 52212887
      }, {
        filename: "/lib/python3.15/xml/dom/pulldom.py",
        start: 52212887,
        end: 52224524
      }, {
        filename: "/lib/python3.15/xml/dom/xmlbuilder.py",
        start: 52224524,
        end: 52236944
      }, {
        filename: "/lib/python3.15/xml/etree/ElementInclude.py",
        start: 52236944,
        end: 52243896
      }, {
        filename: "/lib/python3.15/xml/etree/ElementPath.py",
        start: 52243896,
        end: 52257893
      }, {
        filename: "/lib/python3.15/xml/etree/ElementTree.py",
        start: 52257893,
        end: 52333081
      }, {
        filename: "/lib/python3.15/xml/etree/__init__.py",
        start: 52333081,
        end: 52334686
      }, {
        filename: "/lib/python3.15/xml/etree/__pycache__/ElementPath.cpython-315.pyc",
        start: 52334686,
        end: 52350494
      }, {
        filename: "/lib/python3.15/xml/etree/__pycache__/__init__.cpython-315.pyc",
        start: 52350494,
        end: 52350632
      }, {
        filename: "/lib/python3.15/xml/etree/cElementTree.py",
        start: 52350632,
        end: 52350714
      }, {
        filename: "/lib/python3.15/xml/parsers/__init__.py",
        start: 52350714,
        end: 52350881
      }, {
        filename: "/lib/python3.15/xml/parsers/expat.py",
        start: 52350881,
        end: 52351129
      }, {
        filename: "/lib/python3.15/xml/sax/__init__.py",
        start: 52351129,
        end: 52354661
      }, {
        filename: "/lib/python3.15/xml/sax/_exceptions.py",
        start: 52354661,
        end: 52359360
      }, {
        filename: "/lib/python3.15/xml/sax/expatreader.py",
        start: 52359360,
        end: 52375636
      }, {
        filename: "/lib/python3.15/xml/sax/handler.py",
        start: 52375636,
        end: 52391490
      }, {
        filename: "/lib/python3.15/xml/sax/saxutils.py",
        start: 52391490,
        end: 52403745
      }, {
        filename: "/lib/python3.15/xml/sax/xmlreader.py",
        start: 52403745,
        end: 52416369
      }, {
        filename: "/lib/python3.15/xmlrpc/__init__.py",
        start: 52416369,
        end: 52416407
      }, {
        filename: "/lib/python3.15/xmlrpc/client.py",
        start: 52416407,
        end: 52464968
      }, {
        filename: "/lib/python3.15/xmlrpc/server.py",
        start: 52464968,
        end: 52501810
      }, {
        filename: "/lib/python3.15/zipapp.py",
        start: 52501810,
        end: 52510523
      }, {
        filename: "/lib/python3.15/zipfile/__init__.py",
        start: 52510523,
        end: 52602782
      }, {
        filename: "/lib/python3.15/zipfile/__main__.py",
        start: 52602782,
        end: 52602840
      }, {
        filename: "/lib/python3.15/zipfile/_path/__init__.py",
        start: 52602840,
        end: 52614771
      }, {
        filename: "/lib/python3.15/zipfile/_path/_functools.py",
        start: 52614771,
        end: 52615346
      }, {
        filename: "/lib/python3.15/zipfile/_path/glob.py",
        start: 52615346,
        end: 52618660
      }, {
        filename: "/lib/python3.15/zipimport.py",
        start: 52618660,
        end: 52652304
      }, {
        filename: "/lib/python3.15/zoneinfo/__init__.py",
        start: 52652304,
        end: 52653221
      }, {
        filename: "/lib/python3.15/zoneinfo/__pycache__/__init__.cpython-315.pyc",
        start: 52653221,
        end: 52654358
      }, {
        filename: "/lib/python3.15/zoneinfo/__pycache__/_common.cpython-315.pyc",
        start: 52654358,
        end: 52660071
      }, {
        filename: "/lib/python3.15/zoneinfo/__pycache__/_tzpath.cpython-315.pyc",
        start: 52660071,
        end: 52668317
      }, {
        filename: "/lib/python3.15/zoneinfo/_common.py",
        start: 52668317,
        end: 52673846
      }, {
        filename: "/lib/python3.15/zoneinfo/_tzpath.py",
        start: 52673846,
        end: 52679769
      }, {
        filename: "/lib/python3.15/zoneinfo/_zoneinfo.py",
        start: 52679769,
        end: 52704455
      }],
      remote_package_size: 52704455
    };
    var FS_modeStringToFlags = str => {
      var flagModes = {
        r: 0,
        "r+": 2,
        w: 512 | 64 | 1,
        "w+": 512 | 64 | 2,
        a: 1024 | 64 | 1,
        "a+": 1024 | 64 | 2
      };
      var flags = flagModes[str];
      if (typeof flags == "undefined") {
        throw new Error(`Unknown file open mode: ${str}`)
      }
      return flags
    };
    var FS_getMode = (canRead, canWrite) => {
      var mode = 0;
      if (canRead) mode |= 292 | 73;
      if (canWrite) mode |= 146;
      return mode
    };
    var FS = {
      root: null,
      mounts: [],
      devices: {},
      streamMap: new Map(),
      nextInode: 1,
      nameTable: null,
      initialized: false,
      ignorePermissions: true,
      filesystems: null,
      syncFSRequests: 0,
      readFiles: {},
      ErrnoError: class {
        name = "ErrnoError";
        constructor(errno) {
          this.errno = errno
        }
      },
      FSStream: class {
        shared = {};
        get object() {
          return this.node
        }
        set object(val) {
          this.node = val
        }
        get isRead() {
          return (this.flags & 2097155) !== 1
        }
        get isWrite() {
          return (this.flags & 2097155) !== 0
        }
        get isAppend() {
          return this.flags & 1024
        }
        get flags() {
          return this.shared.flags
        }
        set flags(val) {
          this.shared.flags = val
        }
        get position() {
          return this.shared.position
        }
        set position(val) {
          this.shared.position = val
        }
      },
      FSNode: class {
        node_ops = {};
        stream_ops = {};
        readMode = 292 | 73;
        writeMode = 146;
        mounted = null;
        constructor(parent, name, mode, rdev) {
          if (!parent) {
            parent = this
          }
          this.parent = parent;
          this.mount = parent.mount;
          this.id = FS.nextInode++;
          this.name = name;
          this.mode = mode;
          this.rdev = rdev;
          this.atime = this.mtime = this.ctime = Date.now()
        }
        get read() {
          return (this.mode & this.readMode) === this.readMode
        }
        set read(val) {
          val ? this.mode |= this.readMode : this.mode &= ~this.readMode
        }
        get write() {
          return (this.mode & this.writeMode) === this.writeMode
        }
        set write(val) {
          val ? this.mode |= this.writeMode : this.mode &= ~this.writeMode
        }
        get isFolder() {
          return FS.isDir(this.mode)
        }
        get isDevice() {
          return FS.isChrdev(this.mode)
        }
      },
      lookupPath(path, opts = {}) {
        if (!path) {
          throw new FS.ErrnoError(44)
        }
        opts.follow_mount ??= true;
        if (!PATH.isAbs(path)) {
          path = FS.cwd() + "/" + path
        }
        linkloop: for (var nlinks = 0; nlinks < 40; nlinks++) {
          var parts = path.split("/").filter(p => !!p);
          var current = FS.root;
          var current_path = "/";
          for (var i = 0; i < parts.length; i++) {
            var islast = i === parts.length - 1;
            if (islast && opts.parent) {
              break
            }
            if (parts[i] === ".") {
              continue
            }
            if (parts[i] === "..") {
              current_path = PATH.dirname(current_path);
              if (FS.isRoot(current)) {
                path = current_path + "/" + parts.slice(i + 1).join("/");
                continue linkloop
              } else {
                current = current.parent
              }
              continue
            }
            current_path = PATH.join2(current_path, parts[i]);
            try {
              current = FS.lookupNode(current, parts[i])
            } catch (e) {
              if (e?.errno === 44 && islast && opts.noent_okay) {
                return {
                  path: current_path
                }
              }
              throw e
            }
            if (FS.isMountpoint(current) && (!islast || opts.follow_mount)) {
              current = current.mounted.root
            }
            if (FS.isLink(current.mode) && (!islast || opts.follow)) {
              if (!current.node_ops.readlink) {
                throw new FS.ErrnoError(52)
              }
              var link = current.node_ops.readlink(current);
              if (!PATH.isAbs(link)) {
                link = PATH.dirname(current_path) + "/" + link
              }
              path = link + "/" + parts.slice(i + 1).join("/");
              continue linkloop
            }
          }
          return {
            path: current_path,
            node: current
          }
        }
        throw new FS.ErrnoError(32)
      },
      getPath(node) {
        var path;
        while (true) {
          if (FS.isRoot(node)) {
            var mount = node.mount.mountpoint;
            if (!path) return mount;
            return mount[mount.length - 1] !== "/" ? `${mount}/${path}` : mount + path
          }
          path = path ? `${node.name}/${path}` : node.name;
          node = node.parent
        }
      },
      hashName(parentid, name) {
        var hash = 0;
        for (var i = 0; i < name.length; i++) {
          hash = (hash << 5) - hash + name.charCodeAt(i) | 0
        }
        return (parentid + hash >>> 0) % FS.nameTable.length
      },
      hashAddNode(node) {
        var hash = FS.hashName(node.parent.id, node.name);
        node.name_next = FS.nameTable[hash];
        FS.nameTable[hash] = node
      },
      hashRemoveNode(node) {
        var hash = FS.hashName(node.parent.id, node.name);
        if (FS.nameTable[hash] === node) {
          FS.nameTable[hash] = node.name_next
        } else {
          var current = FS.nameTable[hash];
          while (current) {
            if (current.name_next === node) {
              current.name_next = node.name_next;
              break
            }
            current = current.name_next
          }
        }
      },
      lookupNode(parent, name) {
        var errCode = FS.mayLookup(parent);
        if (errCode) {
          throw new FS.ErrnoError(errCode)
        }
        var hash = FS.hashName(parent.id, name);
        for (var node = FS.nameTable[hash]; node; node = node.name_next) {
          var nodeName = node.name;
          if (node.parent.id === parent.id && nodeName === name) {
            return node
          }
        }
        return FS.lookup(parent, name)
      },
      createNode(parent, name, mode, rdev) {
        var node = new FS.FSNode(parent, name, mode, rdev);
        FS.hashAddNode(node);
        return node
      },
      destroyNode(node) {
        FS.hashRemoveNode(node)
      },
      isRoot(node) {
        return node === node.parent
      },
      isMountpoint(node) {
        return !!node.mounted
      },
      isFile(mode) {
        return (mode & 61440) === 32768
      },
      isDir(mode) {
        return (mode & 61440) === 16384
      },
      isLink(mode) {
        return (mode & 61440) === 40960
      },
      isChrdev(mode) {
        return (mode & 61440) === 8192
      },
      isBlkdev(mode) {
        return (mode & 61440) === 24576
      },
      isFIFO(mode) {
        return (mode & 61440) === 4096
      },
      isSocket(mode) {
        return (mode & 49152) === 49152
      },
      flagsToPermissionString(flag) {
        var perms = ["r", "w", "rw"][flag & 3];
        if (flag & 512) {
          perms += "w"
        }
        return perms
      },
      nodePermissions(node, perms) {
        if (FS.ignorePermissions) {
          return 0
        }
        if (perms.includes("r") && !(node.mode & 292)) {
          return 2
        } else if (perms.includes("w") && !(node.mode & 146)) {
          return 2
        } else if (perms.includes("x") && !(node.mode & 73)) {
          return 2
        }
        return 0
      },
      mayLookup(dir) {
        if (!FS.isDir(dir.mode)) return 54;
        var errCode = FS.nodePermissions(dir, "x");
        if (errCode) return errCode;
        if (!dir.node_ops.lookup) return 2;
        return 0
      },
      mayCreate(dir, name) {
        if (!FS.isDir(dir.mode)) {
          return 54
        }
        try {
          var node = FS.lookupNode(dir, name);
          return 20
        } catch (e) { }
        return FS.nodePermissions(dir, "wx")
      },
      mayDelete(dir, name, isdir) {
        var node;
        try {
          node = FS.lookupNode(dir, name)
        } catch (e) {
          return e.errno
        }
        var errCode = FS.nodePermissions(dir, "wx");
        if (errCode) {
          return errCode
        }
        if (isdir) {
          if (!FS.isDir(node.mode)) {
            return 54
          }
          if (FS.isRoot(node) || FS.getPath(node) === FS.cwd()) {
            return 10
          }
        } else {
          if (FS.isDir(node.mode)) {
            return 31
          }
        }
        return 0
      },
      mayOpen(node, flags) {
        if (!node) {
          return 44
        }
        if (FS.isLink(node.mode)) {
          return 32
        } else if (FS.isDir(node.mode)) {
          if (FS.flagsToPermissionString(flags) !== "r" || flags & (512 | 64)) {
            return 31
          }
        }
        return FS.nodePermissions(node, FS.flagsToPermissionString(flags))
      },
      checkOpExists(op, err) {
        if (!op) {
          throw new FS.ErrnoError(err)
        }
        return op
      },
      MAX_OPEN_FDS: 4096,
      nextfd() {
        for (var fd = 0; fd <= FS.MAX_OPEN_FDS; fd++) {
          if (!FS.streamMap.get(tEcvPid).get(fd)) {
            return fd
          }
        }
        throw new FS.ErrnoError(33)
      },
      getStreamChecked(fd) {
        var stream = FS.getStream(fd);
        if (!stream) {
          throw new FS.ErrnoError(8)
        }
        return stream
      },
      getStream: fd => FS.streamMap.get(tEcvPid).get(fd),
      createStream(stream, fd = -1) {
        stream = Object.assign(new FS.FSStream, stream);
        if (fd == -1) {
          fd = FS.nextfd()
        }
        stream.fd = fd;
        FS.streamMap.get(tEcvPid).set(fd, stream);
        return stream
      },
      closeStream(fd) {
        FS.streamMap.get(tEcvPid).delete(fd);
      },
      dupStream(origStream, fd = -1) {
        var stream = FS.createStream(origStream, fd);
        stream.stream_ops?.dup?.(stream);
        return stream
      },
      doSetAttr(stream, node, attr) {
        var setattr = stream?.stream_ops.setattr;
        var arg = setattr ? stream : node;
        setattr ??= node.node_ops.setattr;
        FS.checkOpExists(setattr, 63);
        setattr(arg, attr)
      },
      chrdev_stream_ops: {
        open(stream) {
          var device = FS.getDevice(stream.node.rdev);
          stream.stream_ops = device.stream_ops;
          stream.stream_ops.open?.(stream)
        },
        llseek() {
          throw new FS.ErrnoError(70)
        }
      },
      major: dev => dev >> 8,
      minor: dev => dev & 255,
      makedev: (ma, mi) => ma << 8 | mi,
      registerDevice(dev, ops) {
        FS.devices[dev] = {
          stream_ops: ops
        }
      },
      getDevice: dev => FS.devices[dev],
      getMounts(mount) {
        var mounts = [];
        var check = [mount];
        while (check.length) {
          var m = check.pop();
          mounts.push(m);
          check.push(...m.mounts)
        }
        return mounts
      },
      syncfs(populate, callback) {
        if (typeof populate == "function") {
          callback = populate;
          populate = false
        }
        FS.syncFSRequests++;
        if (FS.syncFSRequests > 1) {
          err(`warning: ${FS.syncFSRequests} FS.syncfs operations in flight at once, probably just doing extra work`)
        }
        var mounts = FS.getMounts(FS.root.mount);
        var completed = 0;

        function doCallback(errCode) {
          FS.syncFSRequests--;
          return callback(errCode)
        }

        function done(errCode) {
          if (errCode) {
            if (!done.errored) {
              done.errored = true;
              return doCallback(errCode)
            }
            return
          }
          if (++completed >= mounts.length) {
            doCallback(null)
          }
        }
        mounts.forEach(mount => {
          if (!mount.type.syncfs) {
            return done(null)
          }
          mount.type.syncfs(mount, populate, done)
        })
      },
      mount(type, opts, mountpoint) {
        var root = mountpoint === "/";
        var pseudo = !mountpoint;
        var node;
        if (root && FS.root) {
          throw new FS.ErrnoError(10)
        } else if (!root && !pseudo) {
          var lookup = FS.lookupPath(mountpoint, {
            follow_mount: false
          });
          mountpoint = lookup.path;
          node = lookup.node;
          if (FS.isMountpoint(node)) {
            throw new FS.ErrnoError(10)
          }
          if (!FS.isDir(node.mode)) {
            throw new FS.ErrnoError(54)
          }
        }
        var mount = {
          type,
          opts,
          mountpoint,
          mounts: []
        };
        var mountRoot = type.mount(mount);
        mountRoot.mount = mount;
        mount.root = mountRoot;
        if (root) {
          FS.root = mountRoot
        } else if (node) {
          node.mounted = mount;
          if (node.mount) {
            node.mount.mounts.push(mount)
          }
        }
        return mountRoot
      },
      unmount(mountpoint) {
        var lookup = FS.lookupPath(mountpoint, {
          follow_mount: false
        });
        if (!FS.isMountpoint(lookup.node)) {
          throw new FS.ErrnoError(28)
        }
        var node = lookup.node;
        var mount = node.mounted;
        var mounts = FS.getMounts(mount);
        Object.keys(FS.nameTable).forEach(hash => {
          var current = FS.nameTable[hash];
          while (current) {
            var next = current.name_next;
            if (mounts.includes(current.mount)) {
              FS.destroyNode(current)
            }
            current = next
          }
        });
        node.mounted = null;
        var idx = node.mount.mounts.indexOf(mount);
        node.mount.mounts.splice(idx, 1)
      },
      lookup(parent, name) {
        return parent.node_ops.lookup(parent, name)
      },
      mknod(path, mode, dev) {
        var lookup = FS.lookupPath(path, {
          parent: true
        });
        var parent = lookup.node;
        var name = PATH.basename(path);
        if (!name) {
          throw new FS.ErrnoError(28)
        }
        if (name === "." || name === "..") {
          throw new FS.ErrnoError(20)
        }
        var errCode = FS.mayCreate(parent, name);
        if (errCode) {
          throw new FS.ErrnoError(errCode)
        }
        if (!parent.node_ops.mknod) {
          throw new FS.ErrnoError(63)
        }
        return parent.node_ops.mknod(parent, name, mode, dev)
      },
      statfs(path) {
        return FS.statfsNode(FS.lookupPath(path, {
          follow: true
        }).node)
      },
      statfsStream(stream) {
        return FS.statfsNode(stream.node)
      },
      statfsNode(node) {
        var rtn = {
          bsize: 4096,
          frsize: 4096,
          blocks: 1e6,
          bfree: 5e5,
          bavail: 5e5,
          files: FS.nextInode,
          ffree: FS.nextInode - 1,
          fsid: 42,
          flags: 2,
          namelen: 255
        };
        if (node.node_ops.statfs) {
          Object.assign(rtn, node.node_ops.statfs(node.mount.opts.root))
        }
        return rtn
      },
      create(path, mode = 438) {
        mode &= 4095;
        mode |= 32768;
        return FS.mknod(path, mode, 0)
      },
      mkdir(path, mode = 511) {
        mode &= 511 | 512;
        mode |= 16384;
        return FS.mknod(path, mode, 0)
      },
      mkdirTree(path, mode) {
        var dirs = path.split("/");
        var d = "";
        for (var dir of dirs) {
          if (!dir) continue;
          if (d || PATH.isAbs(path)) d += "/";
          d += dir;
          try {
            FS.mkdir(d, mode)
          } catch (e) {
            if (e.errno != 20) throw e
          }
        }
      },
      mkdev(path, mode, dev) {
        if (typeof dev == "undefined") {
          dev = mode;
          mode = 438
        }
        mode |= 8192;
        return FS.mknod(path, mode, dev)
      },
      symlink(oldpath, newpath) {
        if (!PATH_FS.resolve(oldpath)) {
          throw new FS.ErrnoError(44)
        }
        var lookup = FS.lookupPath(newpath, {
          parent: true
        });
        var parent = lookup.node;
        if (!parent) {
          throw new FS.ErrnoError(44)
        }
        var newname = PATH.basename(newpath);
        var errCode = FS.mayCreate(parent, newname);
        if (errCode) {
          throw new FS.ErrnoError(errCode)
        }
        if (!parent.node_ops.symlink) {
          throw new FS.ErrnoError(63)
        }
        return parent.node_ops.symlink(parent, newname, oldpath)
      },
      pursueSymlink(path) {
        let lookup = FS.lookupPath(path);
        while (lookup.node.link) {
          lookup = FS.lookupPath(lookup.node.link);
        }
        return lookup.path;
      },
      rename(old_path, new_path) {
        var old_dirname = PATH.dirname(old_path);
        var new_dirname = PATH.dirname(new_path);
        var old_name = PATH.basename(old_path);
        var new_name = PATH.basename(new_path);
        var lookup, old_dir, new_dir;
        lookup = FS.lookupPath(old_path, {
          parent: true
        });
        old_dir = lookup.node;
        lookup = FS.lookupPath(new_path, {
          parent: true
        });
        new_dir = lookup.node;
        if (!old_dir || !new_dir) throw new FS.ErrnoError(44);
        if (old_dir.mount !== new_dir.mount) {
          throw new FS.ErrnoError(75)
        }
        var old_node = FS.lookupNode(old_dir, old_name);
        var relative = PATH_FS.relative(old_path, new_dirname);
        if (relative.charAt(0) !== ".") {
          throw new FS.ErrnoError(28)
        }
        relative = PATH_FS.relative(new_path, old_dirname);
        if (relative.charAt(0) !== ".") {
          throw new FS.ErrnoError(55)
        }
        var new_node;
        try {
          new_node = FS.lookupNode(new_dir, new_name)
        } catch (e) { }
        if (old_node === new_node) {
          return
        }
        var isdir = FS.isDir(old_node.mode);
        var errCode = FS.mayDelete(old_dir, old_name, isdir);
        if (errCode) {
          throw new FS.ErrnoError(errCode)
        }
        errCode = new_node ? FS.mayDelete(new_dir, new_name, isdir) : FS.mayCreate(new_dir, new_name);
        if (errCode) {
          throw new FS.ErrnoError(errCode)
        }
        if (!old_dir.node_ops.rename) {
          throw new FS.ErrnoError(63)
        }
        if (FS.isMountpoint(old_node) || new_node && FS.isMountpoint(new_node)) {
          throw new FS.ErrnoError(10)
        }
        if (new_dir !== old_dir) {
          errCode = FS.nodePermissions(old_dir, "w");
          if (errCode) {
            throw new FS.ErrnoError(errCode)
          }
        }
        FS.hashRemoveNode(old_node);
        try {
          old_dir.node_ops.rename(old_node, new_dir, new_name);
          old_node.parent = new_dir
        } catch (e) {
          throw e
        } finally {
          FS.hashAddNode(old_node)
        }
      },
      rmdir(path) {
        var lookup = FS.lookupPath(path, {
          parent: true
        });
        var parent = lookup.node;
        var name = PATH.basename(path);
        var node = FS.lookupNode(parent, name);
        var errCode = FS.mayDelete(parent, name, true);
        if (errCode) {
          throw new FS.ErrnoError(errCode)
        }
        if (!parent.node_ops.rmdir) {
          throw new FS.ErrnoError(63)
        }
        if (FS.isMountpoint(node)) {
          throw new FS.ErrnoError(10)
        }
        parent.node_ops.rmdir(parent, name);
        FS.destroyNode(node)
      },
      readdir(path) {
        var lookup = FS.lookupPath(path, {
          follow: true
        });
        var node = lookup.node;
        var readdir = FS.checkOpExists(node.node_ops.readdir, 54);
        return readdir(node)
      },
      unlink(path) {
        var lookup = FS.lookupPath(path, {
          parent: true
        });
        var parent = lookup.node;
        if (!parent) {
          throw new FS.ErrnoError(44)
        }
        var name = PATH.basename(path);
        var node = FS.lookupNode(parent, name);
        var errCode = FS.mayDelete(parent, name, false);
        if (errCode) {
          throw new FS.ErrnoError(errCode)
        }
        if (!parent.node_ops.unlink) {
          throw new FS.ErrnoError(63)
        }
        if (FS.isMountpoint(node)) {
          throw new FS.ErrnoError(10)
        }
        parent.node_ops.unlink(parent, name);
        FS.destroyNode(node)
      },
      readlink(path) {
        var lookup = FS.lookupPath(path);
        var link = lookup.node;
        if (!link) {
          throw new FS.ErrnoError(44)
        }
        if (!link.node_ops.readlink) {
          throw new FS.ErrnoError(28)
        }
        return link.node_ops.readlink(link)
      },
      stat(path, dontFollow) {
        var lookup = FS.lookupPath(path, {
          follow: !dontFollow
        });
        var node = lookup.node;
        var getattr = FS.checkOpExists(node.node_ops.getattr, 63);
        return getattr(node)
      },
      fstat(fd) {
        var stream = FS.getStreamChecked(fd);
        var node = stream.node;
        var getattr = stream.stream_ops.getattr;
        var arg = getattr ? stream : node;
        getattr ??= node.node_ops.getattr;
        FS.checkOpExists(getattr, 63);
        return getattr(arg)
      },
      lstat(path) {
        return FS.stat(path, true)
      },
      doChmod(stream, node, mode, dontFollow) {
        FS.doSetAttr(stream, node, {
          mode: mode & 4095 | node.mode & ~4095,
          ctime: Date.now(),
          dontFollow
        })
      },
      chmod(path, mode, dontFollow) {
        var node;
        if (typeof path == "string") {
          var lookup = FS.lookupPath(path, {
            follow: !dontFollow
          });
          node = lookup.node
        } else {
          node = path
        }
        FS.doChmod(null, node, mode, dontFollow)
      },
      lchmod(path, mode) {
        FS.chmod(path, mode, true)
      },
      fchmod(fd, mode) {
        var stream = FS.getStreamChecked(fd);
        FS.doChmod(stream, stream.node, mode, false)
      },
      doChown(stream, node, dontFollow) {
        FS.doSetAttr(stream, node, {
          timestamp: Date.now(),
          dontFollow
        })
      },
      chown(path, uid, gid, dontFollow) {
        var node;
        if (typeof path == "string") {
          var lookup = FS.lookupPath(path, {
            follow: !dontFollow
          });
          node = lookup.node
        } else {
          node = path
        }
        FS.doChown(null, node, dontFollow)
      },
      lchown(path, uid, gid) {
        FS.chown(path, uid, gid, true)
      },
      fchown(fd, uid, gid) {
        var stream = FS.getStreamChecked(fd);
        FS.doChown(stream, stream.node, false)
      },
      doTruncate(stream, node, len) {
        if (FS.isDir(node.mode)) {
          throw new FS.ErrnoError(31)
        }
        if (!FS.isFile(node.mode)) {
          throw new FS.ErrnoError(28)
        }
        var errCode = FS.nodePermissions(node, "w");
        if (errCode) {
          throw new FS.ErrnoError(errCode)
        }
        FS.doSetAttr(stream, node, {
          size: len,
          timestamp: Date.now()
        })
      },
      truncate(path, len) {
        if (len < 0) {
          throw new FS.ErrnoError(28)
        }
        var node;
        if (typeof path == "string") {
          var lookup = FS.lookupPath(path, {
            follow: true
          });
          node = lookup.node
        } else {
          node = path
        }
        FS.doTruncate(null, node, len)
      },
      ftruncate(fd, len) {
        var stream = FS.getStreamChecked(fd);
        if (len < 0 || (stream.flags & 2097155) === 0) {
          throw new FS.ErrnoError(28)
        }
        FS.doTruncate(stream, stream.node, len)
      },
      utime(path, atime, mtime) {
        var lookup = FS.lookupPath(path, {
          follow: true
        });
        var node = lookup.node;
        var setattr = FS.checkOpExists(node.node_ops.setattr, 63);
        setattr(node, {
          atime,
          mtime
        })
      },
      open(path, flags, mode = 438) { // 438 = 0o0666
        if (path === "") {
          throw new FS.ErrnoError(44)
        }
        flags = typeof flags == "string" ? FS_modeStringToFlags(flags) : flags;
        if (flags & 64) {
          mode = mode & 4095 | 32768
        } else {
          mode = 0
        }
        var node;
        var isDirPath;
        if (typeof path == "object") {
          node = path
        } else {
          isDirPath = path.endsWith("/");
          var lookup = FS.lookupPath(path, {
            follow: !(flags & 131072),
            noent_okay: true
          });
          node = lookup.node;
          path = lookup.path
        }
        var created = false;
        if (flags & 64) {
          if (node) {
            if (flags & 128) {
              throw new FS.ErrnoError(20)
            }
          } else if (isDirPath) {
            throw new FS.ErrnoError(31)
          } else {
            node = FS.mknod(path, mode | 511, 0);
            created = true
          }
        }
        if (!node) {
          throw new FS.ErrnoError(44)
        }
        if (FS.isChrdev(node.mode)) {
          flags &= ~512
        }
        if (flags & 65536 && !FS.isDir(node.mode)) {
          throw new FS.ErrnoError(54)
        }
        if (!created) {
          var errCode = FS.mayOpen(node, flags);
          if (errCode) {
            throw new FS.ErrnoError(errCode)
          }
        }
        if (flags & 512 && !created) {
          FS.truncate(node, 0)
        }
        var seekable = false;
        if (!FS.isFIFO(node.mode)) {
          seekable = true;
        }
        let fd_flags = flags & O_CLOEXEC ? FD_CLOEXEC : 0;
        flags &= ~(128 | 512 | 131072);
        var stream = FS.createStream({
          node,
          path: FS.getPath(node),
          flags,
          fd_flags,
          seekable: seekable,
          position: 0,
          stream_ops: node.stream_ops,
          ungotten: [],
          error: false
        });
        if (stream.stream_ops.open) {
          stream.stream_ops.open(stream)
        }
        if (created) {
          FS.chmod(node, mode & 511)
        }
        if (Module["logReadFiles"] && !(flags & 1)) {
          if (!(path in FS.readFiles)) {
            FS.readFiles[path] = 1
          }
        }
        return stream
      },
      close(fd) {
        if (FS.isClosed(fd)) {
          throw new FS.ErrnoError(8)
        }
        let stream = SYSCALLS.getStreamFromFD(fd);
        if (stream.getdents) stream.getdents = null;
        try {
          if (stream.stream_ops.close) {
            stream.stream_ops.close(stream)
          }
        } catch (e) {
          throw e
        } finally {
          FS.closeStream(fd)
        }
      },
      isClosed(fd) {
        return !FS.streamMap.get(tEcvPid).has(fd);
      },
      initFDTable(ecvPid, parEcvPid) {
        if (!FS.streamMap.has(ecvPid)) {
          FS.streamMap.set(ecvPid, new Map());
        }
        if (parEcvPid == 0) {
          return;
        }
        for (var [fd, stream] of FS.streamMap.get(parEcvPid)) {
          FS.streamMap.get(ecvPid).set(fd, stream);
        }
      },
      closeOnExecFD(ecvPid) {
        for (var [fd, stream] of FS.streamMap.get(ecvPid)) {
          if (stream.fd_flags & FD_CLOEXEC) {
            FS.close(fd);
          }
        }
      },
      llseek(stream, offset, whence) {
        if (FS.isClosed(stream.fd)) {
          throw new FS.ErrnoError(8)
        }
        if (!stream.seekable || !stream.stream_ops.llseek) {
          throw new FS.ErrnoError(70)
        }
        if (whence != 0 && whence != 1 && whence != 2) {
          throw new FS.ErrnoError(28)
        }
        stream.position = stream.stream_ops.llseek(stream, offset, whence);
        stream.ungotten = [];
        return stream.position
      },
      read(stream, buffer, offset, length, position) {
        if (length < 0 || position < 0) {
          throw new FS.ErrnoError(28)
        }
        if (FS.isClosed(stream.fd)) {
          throw new FS.ErrnoError(8)
        }
        if ((stream.flags & 2097155) === 1) {
          throw new FS.ErrnoError(8)
        }
        if (FS.isDir(stream.node.mode)) {
          throw new FS.ErrnoError(31)
        }
        if (!stream.stream_ops.read) {
          throw new FS.ErrnoError(28)
        }
        var seeking = typeof position != "undefined";
        if (!seeking) {
          position = stream.position
        } else if (!stream.seekable) {
          throw new FS.ErrnoError(70)
        }
        var bytesRead = stream.stream_ops.read(stream, buffer, offset, length, position);
        if (!seeking) stream.position += bytesRead;
        return bytesRead
      },
      write(stream, buffer, offset, length, position, canOwn) {
        if (length < 0 || position < 0) {
          throw new FS.ErrnoError(28)
        }
        if (FS.isClosed(stream.fd)) {
          throw new FS.ErrnoError(8)
        }
        if ((stream.flags & 2097155) === 0) {
          throw new FS.ErrnoError(8)
        }
        if (FS.isDir(stream.node.mode)) {
          throw new FS.ErrnoError(31)
        }
        if (!stream.stream_ops.write) {
          throw new FS.ErrnoError(28)
        }
        if (stream.seekable && stream.flags & 1024) {
          FS.llseek(stream, 0, 2)
        }
        var seeking = typeof position != "undefined";
        if (!seeking) {
          position = stream.position
        } else if (!stream.seekable) {
          throw new FS.ErrnoError(70)
        }
        var bytesWritten = stream.stream_ops.write(stream, buffer, offset, length, position, canOwn);
        if (!seeking) stream.position += bytesWritten;
        return bytesWritten
      },
      mmap(stream, length, position, prot, flags) {
        if ((prot & 2) !== 0 && (flags & 2) === 0 && (stream.flags & 2097155) !== 2) {
          throw new FS.ErrnoError(2)
        }
        if ((stream.flags & 2097155) === 1) {
          throw new FS.ErrnoError(2)
        }
        if (!stream.stream_ops.mmap) {
          throw new FS.ErrnoError(43)
        }
        if (!length) {
          throw new FS.ErrnoError(28)
        }
        return stream.stream_ops.mmap(stream, length, position, prot, flags)
      },
      msync(stream, buffer, offset, length, mmapFlags) {
        if (!stream.stream_ops.msync) {
          return 0
        }
        return stream.stream_ops.msync(stream, buffer, offset, length, mmapFlags)
      },
      ioctl(stream, cmd, arg) {
        if (!stream.stream_ops.ioctl) {
          throw new FS.ErrnoError(59)
        }
        return stream.stream_ops.ioctl(stream, cmd, arg)
      },
      readFile(path, opts = {}) {
        opts.flags = opts.flags || 0;
        opts.encoding = opts.encoding || "binary";
        if (opts.encoding !== "utf8" && opts.encoding !== "binary") {
          throw new Error(`Invalid encoding type "${opts.encoding}"`)
        }
        var ret;
        var stream = FS.open(path, opts.flags);
        var stat = FS.stat(path);
        var length = stat.size;
        var buf = new Uint8Array(length);
        FS.read(stream, buf, 0, length, 0);
        if (opts.encoding === "utf8") {
          ret = UTF8ArrayToString(buf)
        } else if (opts.encoding === "binary") {
          ret = buf
        }
        FS.close(stream.fd);
        return ret
      },
      writeFile(path, data, opts = {}) {
        opts.flags = opts.flags || 577;
        var stream = FS.open(path, opts.flags, opts.mode);
        if (typeof data == "string") {
          var buf = new Uint8Array(lengthBytesUTF8(data) + 1);
          var actualNumBytes = stringToUTF8Array(data, buf, 0, buf.length);
          FS.write(stream, buf, 0, actualNumBytes, undefined, opts.canOwn)
        } else if (ArrayBuffer.isView(data)) {
          FS.write(stream, data, 0, data.byteLength, undefined, opts.canOwn)
        } else {
          throw new Error("Unsupported data type")
        }
        FS.close(stream.fd)
      },
      cwd: () => processes.get(tEcvPid).task.fs_struct.pwd,
      chdir(path) {
        var lookup = FS.lookupPath(path, {
          follow: true
        });
        if (lookup.node === null) {
          throw new FS.ErrnoError(44)
        }
        if (!FS.isDir(lookup.node.mode)) {
          throw new FS.ErrnoError(54)
        }
        var errCode = FS.nodePermissions(lookup.node, "x");
        if (errCode) {
          throw new FS.ErrnoError(errCode)
        }
        processes.get(tEcvPid).task.fs_struct.pwd = lookup.path
      },
      createDefaultDirectories() {
        FS.mkdir("/tmp");
        FS.mkdir("/home");
        FS.mkdir("/home/web_user");
        FS.mkdir("/usr");
        FS.mkdir("/usr/bin");
      },
      createDefaultDevices() {
        FS.mkdir("/dev");
        FS.registerDevice(FS.makedev(1, 3), {
          read: () => 0,
          write: (stream, buffer, offset, length, pos) => length,
          llseek: () => 0
        });
        FS.mkdev("/dev/null", FS.makedev(1, 3));
        TTY.register(FS.makedev(5, 0), TTY.default_tty_ops);
        TTY.register(FS.makedev(6, 0), TTY.default_tty1_ops);
        FS.mkdev("/dev/tty", FS.makedev(5, 0));
        FS.mkdev("/dev/tty1", FS.makedev(6, 0));
        var randomBuffer = new Uint8Array(1024),
          randomLeft = 0;
        var randomByte = () => {
          if (randomLeft === 0) {
            randomFill(randomBuffer);
            randomLeft = randomBuffer.byteLength
          }
          return randomBuffer[--randomLeft]
        };
        FS.createDevice("/dev", "random", randomByte);
        FS.createDevice("/dev", "urandom", randomByte);
        FS.mkdir("/dev/shm");
        FS.mkdir("/dev/shm/tmp");
        FS.mkdir("/dev/pipe2");
      },
      createStandardStreams(input, output, error) {
        if (input) {
          FS.createDevice("/dev", "stdin", input)
        } else {
          FS.symlink("/dev/tty", "/dev/stdin")
        }
        if (output) {
          FS.createDevice("/dev", "stdout", null, output)
        } else {
          FS.symlink("/dev/tty", "/dev/stdout")
        }
        if (error) {
          FS.createDevice("/dev", "stderr", null, error)
        } else {
          FS.symlink("/dev/tty", "/dev/stderr")
        }
        var stdin = FS.open("/dev/stdin", 0); // fd = 0
        var stdout = FS.open("/dev/stdout", 1); // fd = 1
        var stderr = FS.open("/dev/stderr", 1); // fd = 2
      },
      createUserSymlinks(cmdMap) {
        for (var [link, bin] of cmdMap) {
          FS.symlink(`/usr/bin/${bin}`, `/usr/bin/${link}`);
        }
      },
      createUserExecutableFiles(userBinList) {
        let userBinSet = [...new Set(userBinList)];
        for (let bin of userBinSet) {
          FS.open("/usr/bin/" + bin, O_CREAT, S_IRWXU | S_IRGRP | S_IWGRP | S_IROTH);
          if (bin === "busybox") {
            this.createUserSymlinks(new Map([
              ["arch", "busybox"],
              ["ascii", "busybox"],
              ["basename", "busybox"],
              ["chmod", "busybox"],
              ["chown", "busybox"],
              ["clear", "busybox"],
              ["cp", "busybox"],
              ["date", "busybox"],
              ["dirname", "busybox"],
              ["expr", "busybox"],
              ["head", "busybox"],
              ["hostname", "busybox"],
              ["ln", "busybox"],
              ["ls", "busybox"],
              ["mkdir", "busybox"],
              ["mv", "busybox"],
              ["rm", "busybox"],
              ["rmdir", "busybox"],
              ["seq", "busybox"],
              ["sleep", "busybox"],
              ["tail", "busybox"],
              ["top", "busybox"],
              ["tree", "busybox"],
              ["uname", "busybox"],
              ["uptime", "busybox"],
              ["vi", "busybox"],
              ["cat", "busybox"],
              ["touch", "busybox"],
              ["ps", "busybox"],
              ["wc", "busybox"],
              ["awk", "busybox"],
              ["base64", "busybox"],
              ["cal", "busybox"],
              ["cksum", "busybox"],
              ["cmp", "busybox"],
              ["comm", "busybox"],
              ["cut", "busybox"],
              ["dd", "busybox"],
              ["diff", "busybox"],
              ["dos2unix", "busybox"],
              ["du", "busybox"],
              ["echo", "busybox"],
              ["ed", "busybox"],
              ["env", "busybox"],
              ["expand", "busybox"],
              ["factor", "busybox"],
              ["false", "busybox"],
              ["find", "busybox"],
              ["fold", "busybox"],
              ["free", "busybox"],
              ["grep", "busybox"],
              ["egrep", "busybox"],
              ["fgrep", "busybox"],
              ["groups", "busybox"],
              ["hd", "busybox"],
              ["hexdump", "busybox"],
              ["id", "busybox"],
              ["less", "busybox"],
              ["link", "busybox"],
              ["logname", "busybox"],
              ["md5sum", "busybox"],
              ["mktemp", "busybox"],
              ["more", "busybox"],
              ["nl", "busybox"],
              ["nproc", "busybox"],
              ["od", "busybox"],
              ["paste", "busybox"],
              ["printenv", "busybox"],
              ["printf", "busybox"],
              ["pwd", "busybox"],
              ["readlink", "busybox"],
              ["realpath", "busybox"],
              ["reset", "busybox"],
              ["rev", "busybox"],
              ["sed", "busybox"],
              ["sha1sum", "busybox"],
              ["sha256sum", "busybox"],
              ["sha512sum", "busybox"],
              ["shuf", "busybox"],
              ["sort", "busybox"],
              ["stat", "busybox"],
              ["strings", "busybox"],
              ["stty", "busybox"],
              ["sum", "busybox"],
              ["tac", "busybox"],
              ["tee", "busybox"],
              ["test", "busybox"],
              ["time", "busybox"],
              ["timeout", "busybox"],
              ["tr", "busybox"],
              ["true", "busybox"],
              ["truncate", "busybox"],
              ["tsort", "busybox"],
              ["tty", "busybox"],
              ["uniq", "busybox"],
              ["unix2dos", "busybox"],
              ["unlink", "busybox"],
              ["usleep", "busybox"],
              ["users", "busybox"],
              ["w", "busybox"],
              ["which", "busybox"],
              ["who", "busybox"],
              ["whoami", "busybox"],
              ["xargs", "busybox"],
              ["xxd", "busybox"],
              ["yes", "busybox"]
            ]));
          }
        }
      },
      staticInit() {
        FS.nameTable = new Array(4096);
        FS.mount(MEMFS, {}, "/");
        FS.createDefaultDirectories();
        FS.createDefaultDevices();
        FS.filesystems = {
          MEMFS
        }
      },
      initStandardStream(input, output, error) {
        FS.initialized = true;
        input ??= Module["stdin"];
        output ??= Module["stdout"];
        error ??= Module["stderr"];
        FS.createStandardStreams(input, output, error);
        // locate the all user Wasm program on `/usr/bin`.
        FS.createUserExecutableFiles(userBinList);
      },
      quit() {
        FS.initialized = false;
        for (var [fd, stream] of FS.streamMap.get(tEcvPid)) {
          if (stream) {
            FS.close(stream.fd)
          }
        }
      },
      findObject(path, dontResolveLastLink) {
        var ret = FS.analyzePath(path, dontResolveLastLink);
        if (!ret.exists) {
          return null
        }
        return ret.object
      },
      analyzePath(path, dontResolveLastLink) {
        try {
          var lookup = FS.lookupPath(path, {
            follow: !dontResolveLastLink
          });
          path = lookup.path
        } catch (e) { }
        var ret = {
          isRoot: false,
          exists: false,
          error: 0,
          name: null,
          path: null,
          object: null,
          parentExists: false,
          parentPath: null,
          parentObject: null
        };
        try {
          var lookup = FS.lookupPath(path, {
            parent: true
          });
          ret.parentExists = true;
          ret.parentPath = lookup.path;
          ret.parentObject = lookup.node;
          ret.name = PATH.basename(path);
          lookup = FS.lookupPath(path, {
            follow: !dontResolveLastLink
          });
          ret.exists = true;
          ret.path = lookup.path;
          ret.object = lookup.node;
          ret.name = lookup.node.name;
          ret.isRoot = lookup.path === "/"
        } catch (e) {
          ret.error = e.errno
        }
        return ret
      },
      createPath(parent, path, canRead, canWrite) {
        parent = typeof parent == "string" ? parent : FS.getPath(parent);
        var parts = path.split("/").reverse();
        while (parts.length) {
          var part = parts.pop();
          if (!part) continue;
          var current = PATH.join2(parent, part);
          try {
            FS.mkdir(current)
          } catch (e) {
            if (e.errno != 20) throw e
          }
          parent = current
        }
        return current
      },
      createFile(parent, name, properties, canRead, canWrite) {
        var path = PATH.join2(typeof parent == "string" ? parent : FS.getPath(parent), name);
        var mode = FS_getMode(canRead, canWrite);
        return FS.create(path, mode)
      },
      createDataFile(parent, name, data, canRead, canWrite, canOwn) {
        var path = name;
        if (parent) {
          parent = typeof parent == "string" ? parent : FS.getPath(parent);
          path = name ? PATH.join2(parent, name) : parent
        }
        var mode = FS_getMode(canRead, canWrite);
        var node = FS.create(path, mode);
        if (data) {
          if (typeof data == "string") {
            var arr = new Array(data.length);
            for (var i = 0, len = data.length; i < len; ++i) arr[i] = data.charCodeAt(i);
            data = arr
          }
          FS.chmod(node, mode | 146);
          var stream = FS.open(node, 577);
          FS.write(stream, data, 0, data.length, 0, canOwn);
          FS.close(stream.fd);
          FS.chmod(node, mode)
        }
      },
      createDevice(parent, name, input, output) {
        var path = PATH.join2(typeof parent == "string" ? parent : FS.getPath(parent), name);
        var mode = FS_getMode(!!input, !!output);
        FS.createDevice.major ??= 64;
        var dev = FS.makedev(FS.createDevice.major++, 0);
        FS.registerDevice(dev, {
          open(stream) {
            stream.seekable = false
          },
          close(stream) {
            if (output?.buffer?.length) {
              output(10)
            }
          },
          read(stream, buffer, offset, length, pos) {
            var bytesRead = 0;
            for (var i = 0; i < length; i++) {
              var result;
              try {
                result = input()
              } catch (e) {
                throw new FS.ErrnoError(29)
              }
              if (result === undefined && bytesRead === 0) {
                throw new FS.ErrnoError(6)
              }
              if (result === null || result === undefined) break;
              bytesRead++;
              buffer[offset + i] = result
            }
            if (bytesRead) {
              stream.node.atime = Date.now()
            }
            return bytesRead
          },
          write(stream, buffer, offset, length, pos) {
            for (var i = 0; i < length; i++) {
              try {
                output(buffer[offset + i])
              } catch (e) {
                throw new FS.ErrnoError(29)
              }
            }
            if (length) {
              stream.node.mtime = stream.node.ctime = Date.now()
            }
            return i
          }
        });
        return FS.mkdev(path, mode, dev)
      },
      forceLoadFile(obj) {
        if (obj.isDevice || obj.isFolder || obj.link || obj.contents) return true;
        if (typeof XMLHttpRequest != "undefined") {
          throw new Error("Lazy loading should have been performed (contents set) in createLazyFile, but it was not. Lazy loading only works in web workers. Use --embed-file or --preload-file in emcc on the main thread.")
        } else {
          try {
            obj.contents = readBinary(obj.url);
            obj.usedBytes = obj.contents.length
          } catch (e) {
            throw new FS.ErrnoError(29)
          }
        }
      },
      createLazyFile(parent, name, url, canRead, canWrite) {
        class LazyUint8Array {
          lengthKnown = false;
          chunks = [];
          get(idx) {
            if (idx > this.length - 1 || idx < 0) {
              return undefined
            }
            var chunkOffset = idx % this.chunkSize;
            var chunkNum = idx / this.chunkSize | 0;
            return this.getter(chunkNum)[chunkOffset]
          }
          setDataGetter(getter) {
            this.getter = getter
          }
          cacheLength() {
            var xhr = new XMLHttpRequest;
            xhr.open("HEAD", url, false);
            xhr.send(null);
            if (!(xhr.status >= 200 && xhr.status < 300 || xhr.status === 304)) throw new Error("Couldn't load " + url + ". Status: " + xhr.status);
            var datalength = Number(xhr.getResponseHeader("Content-length"));
            var header;
            var hasByteServing = (header = xhr.getResponseHeader("Accept-Ranges")) && header === "bytes";
            var usesGzip = (header = xhr.getResponseHeader("Content-Encoding")) && header === "gzip";
            var chunkSize = 1024 * 1024;
            if (!hasByteServing) chunkSize = datalength;
            var doXHR = (from, to) => {
              if (from > to) throw new Error("invalid range (" + from + ", " + to + ") or no bytes requested!");
              if (to > datalength - 1) throw new Error("only " + datalength + " bytes available! programmer error!");
              var xhr = new XMLHttpRequest;
              xhr.open("GET", url, false);
              if (datalength !== chunkSize) xhr.setRequestHeader("Range", "bytes=" + from + "-" + to);
              xhr.responseType = "arraybuffer";
              if (xhr.overrideMimeType) {
                xhr.overrideMimeType("text/plain; charset=x-user-defined")
              }
              xhr.send(null);
              if (!(xhr.status >= 200 && xhr.status < 300 || xhr.status === 304)) throw new Error("Couldn't load " + url + ". Status: " + xhr.status);
              if (xhr.response !== undefined) {
                return new Uint8Array(xhr.response || [])
              }
              return intArrayFromString(xhr.responseText || "", true)
            };
            var lazyArray = this;
            lazyArray.setDataGetter(chunkNum => {
              var start = chunkNum * chunkSize;
              var end = (chunkNum + 1) * chunkSize - 1;
              end = Math.min(end, datalength - 1);
              if (typeof lazyArray.chunks[chunkNum] == "undefined") {
                lazyArray.chunks[chunkNum] = doXHR(start, end)
              }
              if (typeof lazyArray.chunks[chunkNum] == "undefined") throw new Error("doXHR failed!");
              return lazyArray.chunks[chunkNum]
            });
            if (usesGzip || !datalength) {
              chunkSize = datalength = 1;
              datalength = this.getter(0).length;
              chunkSize = datalength;
              out("LazyFiles on gzip forces download of the whole file when length is accessed")
            }
            this._length = datalength;
            this._chunkSize = chunkSize;
            this.lengthKnown = true
          }
          get length() {
            if (!this.lengthKnown) {
              this.cacheLength()
            }
            return this._length
          }
          get chunkSize() {
            if (!this.lengthKnown) {
              this.cacheLength()
            }
            return this._chunkSize
          }
        }
        if (typeof XMLHttpRequest != "undefined") {
          if (!ENVIRONMENT_IS_WORKER) throw "Cannot do synchronous binary XHRs outside webworkers in modern browsers. Use --embed-file or --preload-file in emcc";
          var lazyArray = new LazyUint8Array;
          var properties = {
            isDevice: false,
            contents: lazyArray
          }
        } else {
          var properties = {
            isDevice: false,
            url
          }
        }
        var node = FS.createFile(parent, name, properties, canRead, canWrite);
        if (properties.contents) {
          node.contents = properties.contents
        } else if (properties.url) {
          node.contents = null;
          node.url = properties.url
        }
        Object.defineProperties(node, {
          usedBytes: {
            get: function () {
              return this.contents.length
            }
          }
        });
        var stream_ops = {};
        var keys = Object.keys(node.stream_ops);
        keys.forEach(key => {
          var fn = node.stream_ops[key];
          stream_ops[key] = (...args) => {
            FS.forceLoadFile(node);
            return fn(...args)
          }
        });

        function writeChunks(stream, buffer, offset, length, position) {
          var contents = stream.node.contents;
          if (position >= contents.length) return 0;
          var size = Math.min(contents.length - position, length);
          if (contents.slice) {
            for (var i = 0; i < size; i++) {
              buffer[offset + i] = contents[position + i]
            }
          } else {
            for (var i = 0; i < size; i++) {
              buffer[offset + i] = contents.get(position + i)
            }
          }
          return size
        }
        stream_ops.read = (stream, buffer, offset, length, position) => {
          FS.forceLoadFile(node);
          return writeChunks(stream, buffer, offset, length, position)
        };
        stream_ops.mmap = (stream, length, position, prot, flags) => {
          FS.forceLoadFile(node);
          var ptr = mmapAlloc(length);
          if (!ptr) {
            throw new FS.ErrnoError(48)
          }
          writeChunks(stream, (growMemViews(gWasmMemory), HEAP8), ptr, length, position);
          return {
            ptr,
            allocated: true
          }
        };
        node.stream_ops = stream_ops;
        return node
      }
    };
    var PROCFS = {
      ops_table: null,
      _bootTime: null,
      init(initPid) {
        PROCFS.mount();
        PROCFS._bootTime = Date.now();
        this.createMyProc(initPid);
        // system-wide /proc files
        FS.mknod("/proc/stat", S_IFREG | S_IRUSR | S_IRGRP | S_IROTH, 740);
        FS.mknod("/proc/meminfo", S_IFREG | S_IRUSR | S_IRGRP | S_IROTH, 741);
        FS.mknod("/proc/uptime", S_IFREG | S_IRUSR | S_IRGRP | S_IROTH, 742);
        FS.mknod("/proc/loadavg", S_IFREG | S_IRUSR | S_IRGRP | S_IROTH, 743);
        // /proc/self
        let selfNode = FS.symlink(`/proc/${initPid}`, `/proc/self`);
        // /proc/self/exe for python (FIXME)
        FS.symlink(`/usr/bin/python`, `/proc/self/exe`);
        // /proc/self/maps for python (FIXME)
        FS.mknod(`/proc/self/maps`, S_IFREG | S_IRUSR | S_IRGRP | S_IROTH, 733);
        FS.mkdir(`/proc/self/fd`);
        FS.mount({
          mount() {
            var node = FS.createNode(selfNode, "fd", S_IFDIR | S_IRWXU | S_IRWXG | S_IRWXO, 73);
            node.stream_ops = {
              llseek: MEMFS.stream_ops.llseek
            };
            node.node_ops = {
              lookup(parent, name) {
                var fd = +name;
                var stream = FS.getStreamChecked(fd);
                var ret = {
                  parent: null,
                  mount: {
                    mountpoint: "fake"
                  },
                  node_ops: {
                    readlink: () => stream.path
                  },
                  id: fd + 1
                };
                ret.parent = ret;
                return ret
              },
              readdir() {
                return Array.from(FS.streamMap.get(tEcvPid).entries()).filter(([k, v]) => v).map(([k, v]) => k.toString())
              }
            };
            return node
          }
        }, {}, "/proc/self/fd");
      },
      createMyProc(pid) {
        FS.mkdir(`/proc/${pid}`);
        // /proc/<pid>/stat
        FS.mknod(`/proc/${pid}/stat`, S_IFREG | S_IRUSR | S_IRGRP | S_IROTH, 731);
        // /proc/<pid>/cmdline
        FS.mknod(`/proc/${pid}/cmdline`, S_IFREG | S_IRUSR | S_IRGRP | S_IROTH, 732);
      },
      mount(mount) {
        return PROCFS.createNode(FS.root, `proc`, S_IFDIR | S_IRWXU | S_IRWXG | S_IRWXO, 730);
      },
      createNode(parent, name, mode, dev) {
        if (FS.isBlkdev(mode) || FS.isFIFO(mode)) {
          throw new FS.ErrnoError(63)
        }
        PROCFS.ops_table ||= {
          dir: {
            node: {
              getattr: MEMFS.node_ops.getattr,
              setattr: MEMFS.node_ops.setattr,
              lookup: PROCFS.node_ops.lookup,
              mknod: PROCFS.node_ops.mknod,
              rename: PROCFS.node_ops.rename,
              unlink: PROCFS.node_ops.unlink,
              rmdir: PROCFS.node_ops.rmdir,
              readdir: PROCFS.node_ops.readdir,
              symlink: PROCFS.node_ops.symlink,
            },
            stream: {
              llseek: MEMFS.stream_ops.llseek,
            }
          },
          file: {
            node: {
              getattr: MEMFS.node_ops.getattr,
              setattr: MEMFS.node_ops.setattr,
            },
            stream: {
              llseek: MEMFS.stream_ops.llseek,
              read: PROCFS.stream_ops.read,
              write: PROCFS.stream_ops.write,
            }
          },
          link: {
            node: {
              getattr: MEMFS.node_ops.getattr,
              setattr: MEMFS.node_ops.setattr,
              readlink: MEMFS.node_ops.readlink,
            },
            stream: {},
          }
        };
        let node = FS.createNode(parent, name, mode, dev);
        if (FS.isDir(node.mode)) {
          node.node_ops = PROCFS.ops_table.dir.node;
          node.stream_ops = PROCFS.ops_table.dir.stream;
          node.contents = {};
        } else if (FS.isFile(node.mode)) {
          node.node_ops = PROCFS.ops_table.file.node;
          node.stream_ops = PROCFS.ops_table.file.stream;
          node.usedBytes = 0;
          node.contents = null;
        } else if (FS.isLink(node.mode)) {
          node.node_ops = PROCFS.ops_table.link.node;
          node.stream_ops = PROCFS.ops_table.link.stream;
        }
        node.atime = node.mtime = node.ctime = Date.now();
        if (parent) {
          parent.contents[name] = node;
          parent.atime = parent.mtime = parent.ctime = node.atime
        }
        return node;
      },
      readProcStat(task) {
        const statLine = [
          task.pid,
          `(${task.comm})`,
          task.state,
          task.ppid,
          task.pgrp,
          task.session,

          task.tty_nr,
          task.tpgid,
          task.flags,

          task.minflt,
          task.cminflt,
          task.majflt,
          task.cmajflt,

          task.utime,
          task.stime,
          task.cutime,
          task.cstime,

          task.priority,
          task.nice,

          task.num_threads,
          task.itrealvalue,

          task.starttime,

          task.vsize,
          task.rss,
          task.rsslim,

          task.startcode,
          task.endcode,
          task.startstack,

          task.kstkesp,
          task.kstkeip,

          task.signal,
          task.blocked,
          task.sigignore,
          task.sigcatch,

          task.wchan,
          task.nswap,
          task.cnswap,

          task.exit_signal,
          task.processor,

          task.rt_priority,
          task.policy,

          task.delayacct_blkio_ticks,
          task.guest_time,
          task.cguest_time,

          task.start_data,
          task.end_data,
          task.start_brk,

          task.arg_start,
          task.arg_end,
          task.env_start,
          task.env_end,

          task.exit_code,
        ].join(" ") + "\n";

        return new TextEncoder().encode(statLine).buffer;
      },
      readProcCmdline(task) {
        return new TextEncoder().encode(task.comm).buffer;
      },
      readProcSystemStat() {
        // Minimal /proc/stat for busybox top
        let now = Date.now();
        let uptimeMs = now - PROCFS._bootTime;
        let jiffies = Math.floor(uptimeMs / 10); // USER_HZ=100
        let user = Math.floor(jiffies * 0.05);
        let system = Math.floor(jiffies * 0.02);
        let idle = jiffies - user - system;
        let lines = [
          `cpu  ${user} 0 ${system} ${idle} 0 0 0 0 0 0`,
          `cpu0 ${user} 0 ${system} ${idle} 0 0 0 0 0 0`,
          `intr 0`,
          `ctxt 0`,
          `btime ${Math.floor(PROCFS._bootTime / 1000)}`,
          `processes 1`,
          `procs_running 1`,
          `procs_blocked 0`,
        ];
        return new TextEncoder().encode(lines.join("\n") + "\n").buffer;
      },
      readProcMeminfo() {
        let totalKB = 512 * 1024;
        let freeKB = 256 * 1024;
        let availKB = 384 * 1024;
        let buffersKB = 16 * 1024;
        let cachedKB = 64 * 1024;
        let lines = [
          `MemTotal:       ${totalKB} kB`,
          `MemFree:        ${freeKB} kB`,
          `MemAvailable:   ${availKB} kB`,
          `Buffers:        ${buffersKB} kB`,
          `Cached:         ${cachedKB} kB`,
          `SwapCached:            0 kB`,
          `SwapTotal:             0 kB`,
          `SwapFree:              0 kB`,
        ];
        return new TextEncoder().encode(lines.join("\n") + "\n").buffer;
      },
      readProcUptime() {
        let uptimeSec = ((Date.now() - PROCFS._bootTime) / 1000).toFixed(2);
        let idleSec = (uptimeSec * 0.95).toFixed(2);
        return new TextEncoder().encode(`${uptimeSec} ${idleSec}\n`).buffer;
      },
      readProcLoadavg() {
        return new TextEncoder().encode("0.00 0.00 0.00 1/1 1\n").buffer;
      },
      readProcMaps() {
        // Minimal /proc/self/maps template for your 256MiB arena.
        //
        // Format:
        //   start-end perms offset dev:inode pathname
        //
        // Notes:
        // - addresses are 8-hex digits here (32-bit style) because your arena is 0x00000000..0x10000000
        // - "dev" and "inode" are dummy but plausible.
        // - path is only provided for the main executable mapping.
        //
        // Region plan:
        //  0x00000000..0x00010000  NULL guard (unmapped -> omitted)
        //  0x00010000..0x04000000  Low region (rw-p)
        //  0x04000000..0x0A000000  brk heap (rw-p)
        //  0x0A000000..0x0F000000  mmap region (rw-p)
        //  0x0F000000..0x0F001000  stack guard (---p)
        //  0x0F001000..0x10000000  stack (rw-p)

        const lines = [];

        // Main executable: /usr/bin/python (FIXME)
        // Typical Linux shows multiple segments (r-xp / r--p / rw-p). Keep minimal but plausible.
        // Put it in low region.
        lines.push("00010000-00090000 r-xp 00000000 00:00 0 /usr/bin/python");
        lines.push("00090000-000A0000 r--p 00080000 00:00 0 /usr/bin/python");
        lines.push("000A0000-000B0000 rw-p 00090000 00:00 0 /usr/bin/python");

        // Low region remainder (loader/TLS/static/etc.)
        // We just describe it as anonymous private RW.
        lines.push("000B0000-04000000 rw-p 00000000 00:00 0 [anon:low]");

        // brk heap region (traditional heap)
        lines.push("04000000-0A000000 rw-p 00000000 00:00 0 [heap]");

        // mmap region (anonymous)
        lines.push("0A000000-0F000000 rw-p 00000000 00:00 0 [anon:mmap]");

        // stack guard (no access)
        lines.push("0F000000-0F001000 ---p 00000000 00:00 0 [stack-guard]");

        // stack
        lines.push("0F001000-10000000 rw-p 00000000 00:00 0 [stack]");

        const mapsText = lines.join("\n") + "\n";
        console.log(mapsText);
        return new TextEncoder().encode(mapsText).buffer;
      },
      node_ops: {
        setattr() {
          throw new FS.ErrnoError(30);
        },
        mknod(parent, name, mode, dev) {
          return PROCFS.createNode(parent, name, mode, dev);
        },
        mknodUser() {
          throw new FS.ErrnoError(30);
        },
        lookup(parent, name) {
          throw new FS.ErrnoError(44);
        },
        readdir(node) {
          return [".", "..", ...Object.keys(node.contents)]
        },
        rmdir(parent, name) {
          var node = FS.lookupNode(parent, name);
          for (var childName in node.contents) {
            this.rmdir(node, childName);
          }
          delete parent.contents[name];
          parent.ctime = parent.mtime = Date.now()
        },
        rename() {
          throw new FS.ErrnoError(30);
        },
        unlink() {
          throw new FS.ErrnoError(30);
        },
        symlink(parent, newname, oldpath) {
          var node = PROCFS.createNode(parent, newname, S_IFLNK | S_IRWXU | S_IRWXG | S_IRWXO, 730);
          node.link = oldpath;
          return node;
        },
        symlinkUser() {
          throw new FS.ErrnoError(30);
        },
      },
      stream_ops: {
        read(stream, buffer, offset, length, position) {
          let parent = FS.lookupPath(stream.path, {
            parent: true
          }).node;
          let content;
          // system-wide /proc files (parent is "proc")
          if (parent.name === "proc") {
            switch (stream.node.name) {
              case "stat": content = PROCFS.readProcSystemStat(); break;
              case "meminfo": content = PROCFS.readProcMeminfo(); break;
              case "uptime": content = PROCFS.readProcUptime(); break;
              case "loadavg": content = PROCFS.readProcLoadavg(); break;
              default: throw new FS.ErrnoError(2);
            }
          } else {
            // per-process /proc/<pid>/ files
            let task = processes.get(+(parent.name)).task;
            if (stream.node.name === `stat`) {
              content = PROCFS.readProcStat(task);
            } else if (stream.node.name === `cmdline`) {
              content = PROCFS.readProcCmdline(task);
            } else if (stream.node.name == `maps`) {
              content = PROCFS.readProcMaps();
            } else {
              throw new FS.ErrnoError(2);
            }
          }
          // copy the buffer
          if (position >= content.byteLength) {
            return 0;
          }
          stream.node.usedBytes = content.byteLength; // (FIXME)
          let size = Math.min(content.byteLength - position, length);
          let contentView = new Uint8Array(content);
          if (size > 8) { // for performance improvement.
            buffer.set(contentView, offset);
          } else {
            for (let i = 0; i < size; i++) {
              buffer[offset + i] = contentView[position + i];
            }
          }
          return size;
        },
        write() {
          throw new Error(`write of procfs is not implemented.`);
        },
      }
    };
    var UTF8ToString = (ptr, maxBytesToRead) => ptr ? UTF8ArrayToString((growMemViews(gWasmMemory), HEAPU8), ptr, maxBytesToRead) : "";
    var SYSCALLS = {
      DEFAULT_POLLMASK: POLLIN | POLLOUT | POLLOUT,
      calculateAt(dirfd, path, allowEmpty) {
        if (PATH.isAbs(path)) {
          return path
        }
        var dir;
        if (dirfd === -100) {
          dir = FS.cwd()
        } else {
          var dirstream = SYSCALLS.getStreamFromFD(dirfd);
          dir = dirstream.path
        }
        if (path.length == 0) {
          if (!allowEmpty) {
            throw new FS.ErrnoError(44)
          }
          return dir
        }
        return dir + "/" + path
      },
      writeStat(buf, stat) {
        (growMemViews(gWasmMemory), HEAP32)[buf >> 2] = stat.dev;
        (growMemViews(gWasmMemory), HEAP32)[buf + 4 >> 2] = stat.mode;
        (growMemViews(gWasmMemory), HEAPU32)[buf + 8 >> 2] = stat.nlink;
        (growMemViews(gWasmMemory), HEAP32)[buf + 12 >> 2] = stat.uid;
        (growMemViews(gWasmMemory), HEAP32)[buf + 16 >> 2] = stat.gid;
        (growMemViews(gWasmMemory), HEAP32)[buf + 20 >> 2] = stat.rdev;
        (growMemViews(gWasmMemory), HEAP64)[buf + 24 >> 3] = BigInt(stat.size);
        (growMemViews(gWasmMemory), HEAP32)[buf + 32 >> 2] = 4096;
        (growMemViews(gWasmMemory), HEAP32)[buf + 36 >> 2] = stat.blocks;
        var atime = stat.atime.getTime();
        var mtime = stat.mtime.getTime();
        var ctime = stat.ctime.getTime();
        (growMemViews(gWasmMemory), HEAP64)[buf + 40 >> 3] = BigInt(Math.floor(atime / 1e3));
        (growMemViews(gWasmMemory), HEAPU32)[buf + 48 >> 2] = atime % 1e3 * 1e3 * 1e3;
        (growMemViews(gWasmMemory), HEAP64)[buf + 56 >> 3] = BigInt(Math.floor(mtime / 1e3));
        (growMemViews(gWasmMemory), HEAPU32)[buf + 64 >> 2] = mtime % 1e3 * 1e3 * 1e3;
        (growMemViews(gWasmMemory), HEAP64)[buf + 72 >> 3] = BigInt(Math.floor(ctime / 1e3));
        (growMemViews(gWasmMemory), HEAPU32)[buf + 80 >> 2] = ctime % 1e3 * 1e3 * 1e3;
        (growMemViews(gWasmMemory), HEAP64)[buf + 88 >> 3] = BigInt(stat.ino);
        return 0
      },
      writeStatFs(buf, stats) {
        (growMemViews(gWasmMemory), HEAP32)[buf + 4 >> 2] = stats.bsize;
        (growMemViews(gWasmMemory), HEAP32)[buf + 40 >> 2] = stats.bsize;
        (growMemViews(gWasmMemory), HEAP32)[buf + 8 >> 2] = stats.blocks;
        (growMemViews(gWasmMemory), HEAP32)[buf + 12 >> 2] = stats.bfree;
        (growMemViews(gWasmMemory), HEAP32)[buf + 16 >> 2] = stats.bavail;
        (growMemViews(gWasmMemory), HEAP32)[buf + 20 >> 2] = stats.files;
        (growMemViews(gWasmMemory), HEAP32)[buf + 24 >> 2] = stats.ffree;
        (growMemViews(gWasmMemory), HEAP32)[buf + 28 >> 2] = stats.fsid;
        (growMemViews(gWasmMemory), HEAP32)[buf + 44 >> 2] = stats.flags;
        (growMemViews(gWasmMemory), HEAP32)[buf + 36 >> 2] = stats.namelen
      },
      doMsync(addr, stream, len, flags, offset) {
        if (!FS.isFile(stream.node.mode)) {
          throw new FS.ErrnoError(43)
        }
        if (flags & 2) {
          return 0
        }
        var buffer = (growMemViews(gWasmMemory), HEAPU8).slice(addr, addr + len);
        FS.msync(stream, buffer, offset, len, flags)
      },
      getStreamFromFD(fd) {
        var stream = FS.getStreamChecked(fd);
        return stream
      },
      varargs: undefined,
      getStr(ptr) {
        var ret = UTF8ToString(ptr);
        return ret
      },
      // pipe2
      KERNEL_FIFOS: new Map(),
      pipe2Count: 0,
      getPipe2NewPath() {
        return "/dev/pipe2/node" + (++this.pipe2Count);
      }
    };

    function freeProcessWorker(ecvPid) {
      let thisPr = processes.get(ecvPid);
      processes.get(thisPr.ecvParPid).childs.delete(ecvPid);
      processes.delete(ecvPid);
      FS.streamMap.delete(ecvPid);
      FS.rmdir(`/proc/${ecvPid}`);
      console.log(`Delete process ${ecvPid}. current processes: [${[...processes.keys()]}]`);
    }

    function ___syscall_clone(parEcvPid, sDataP, sDataPLen, mBytes, mBytesLen) {
      try {
        let child_pid = newProcess(initProcessJsPath, true, parEcvPid, sDataP, sDataPLen, mBytes, mBytesLen);
        return child_pid;
      } catch (e) {
        if (typeof FS == "undefined" || !(e.name === "ErrnoError")) throw e;
        return -e.errno;
      }
    }

    function ___syscall_wait4(ecvPid) {

      try {

        let thisEcvPr = processes.get(ecvPid);
        let monitorView = new Int32Array(thisEcvPr.childMonitor);

        // check all bell.
        let ringBell = Atomics.load(monitorView, 0);
        let emptyBell = Atomics.load(monitorView, 1);
        if (ringBell != 1 || emptyBell != 0) {
          throw new Error(`The bell when ___syscall_wait4 is called is strange. ringBell: ${ringBell}, emptyBell: ${emptyBell}`);
        }

        // get the target.
        let head = Atomics.load(monitorView, 2);
        let tail = Atomics.load(monitorView, 3);
        let waitEcvPid = Atomics.load(monitorView, prLingOffset + head);

        // free the target process.
        freeProcessWorker(waitEcvPid);

        // update head.
        let newHead = (head + 1) % childProcessMax;
        Atomics.store(monitorView, 2, newHead);
        if (newHead === tail) {
          // become empty.
          Atomics.store(monitorView, 1, 1);
        }

        return waitEcvPid;

      } catch (e) {
        if (typeof FS == "undefined" || !(e.name === "ErrnoError")) throw e;
        return -e.errno;
      }
    }

    function ___syscall_execve(ecvPid, cmdlineP, argvP, envpP) {
      try {

        let thisPr = processes.get(ecvPid);
        let orgMemory = thisPr.wasmMemory;

        function readByteString(u8View, ptr8) {
          const bytes = [];
          while (u8View[ptr8] !== 0) {
            bytes.push(u8View[ptr8++]);
          }
          return new TextDecoder("utf-8").decode(new Uint8Array(bytes));
        }

        function basename(path) {
          if (!path) return "";

          path = path.replace(/\/+$/, "");

          const idx = path.lastIndexOf("/");
          return idx >= 0 ? path.slice(idx + 1) : path;
        }

        let orgMemU8View = new Uint8Array(orgMemory.buffer);
        let orgMemU32View = new Uint32Array(orgMemory.buffer);

        let tExecPath = FS.pursueSymlink(readByteString(orgMemU8View, cmdlineP));
        let exeName = basename(tExecPath);
        let execveWasm = exeName + '.wasm';
        let execveJs = exeName + '.js';

        console.log(`execveWasm: ${execveWasm}`);

        // get or init worker.
        let workerInfo = WORKER_MGR.getAvailableWorkerInfo(execveJs);
        let execveWorker = workerInfo.worker;
        let newMemory = workerInfo.memory;

        // update initial state
        thisPr.wasmMemory = newMemory;
        thisPr.copyFinBell = new SharedArrayBuffer(4);
        thisPr.wasmProgram = execveWasm;
        thisPr.worker = execveWorker;

        // close the FD of close-on-exec.
        FS.closeOnExecFD(ecvPid);

        // add execve args copy handling to the message handling.
        let initialMsgHandling = execveWorker.onmessage;
        execveWorker.onmessage = e => {
          let d = e["data"];

          tEcvPid = thisPr.ecvPid;

          if (d.cmd === "execveArgsCopy") {

            function countStringBytes(u8View, ptr8) {
              let len = 0;
              while (u8View[ptr8++] !== 0) {
                len++;
              }
              return len;
            }

            let execveBufview = new Int32Array(thisPr.execveBuf);

            // view
            let dst8View = new Int8Array(newMemory.buffer);
            let dst32View = new Int32Array(newMemory.buffer);

            // `argv`
            let argsTotal = 0, argId = 0;
            let srcArgvP32 = argvP >> 2;
            let srcArgvP8 = orgMemU32View[srcArgvP32];
            let dstArgvContentSid = d.argvContentP;
            let cmdline = [];
            while (srcArgvP8) {
              let argSpace = countStringBytes(orgMemU8View, srcArgvP8) + 1; // argSpace includes '\0'
              cmdline.push(readByteString(orgMemU8View, srcArgvP8));
              dst8View.set(orgMemU8View.subarray(srcArgvP8, srcArgvP8 + argSpace), dstArgvContentSid);
              dst32View[(d.argvP >> 2) + argId] = dstArgvContentSid;
              // increment
              srcArgvP32++;
              srcArgvP8 = orgMemU32View[srcArgvP32];
              dstArgvContentSid += argSpace;
              argId++;
              argsTotal += argSpace;
            }
            // default args bytes length threshold is 1,000.
            if (argsTotal >= 1000) {
              throw new Error(`argsTotal is too large at ___syscall_execve. execveWasm: ${execveWasm}, bytes len: ${argId}.`);
            }
            // update task.comm
            thisPr.task.comm = cmdline.join(" ");

            // `argc`
            Atomics.store(execveBufview, 1, argId);

            // `envp`
            let envsTotal, envId = 0;
            let srcEnvpP32 = envpP >> 2;
            let srcEnvpP8 = orgMemU32View[srcEnvpP32];
            let dstEnvpContentSid = d.envpContentP;
            while (srcEnvpP8) {
              let envSpace = countStringBytes(orgMemU8View, srcEnvpP8) + 1; // envSpace includes '\0'
              dst8View.set(orgMemU8View.subarray(srcEnvpP8, srcEnvpP8 + envSpace), dstEnvpContentSid);
              dst32View[(d.envpP >> 2) + envId] = dstEnvpContentSid;
              // increment
              srcEnvpP32++;
              srcEnvpP8 = orgMemU32View[srcEnvpP32];
              dstEnvpContentSid += envSpace;
              envId++;
              envsTotal += envSpace;
            }
            // default envs bytes length threshold is 5,000.
            if (envsTotal >= 5000) {
              throw new Error(`envsTotal is too large at ___syscall_execve. execveWasm: ${execveWasm}, bytes len: ${envId}.`);
            }

            // `ecvPid` (this and parent)
            dst32View[(d.ecvPidsP >> 2)] = thisPr.ecvPid;
            dst32View[(d.ecvPidsP >> 2) + 1] = thisPr.ecvParPid;
            dst32View[(d.ecvPidsP >> 2) + 2] = thisPr.ecvPgid;

            // notify copy success to the new execved worker.
            Atomics.store(execveBufview, 0, 3);
            // notify `two` workers (original worker and new worker).
            Atomics.notify(execveBufview, 0, 2);
          } else {
            initialMsgHandling(e);
          }

          tEcvPid = -1;
        };

        let execveBufView = new Int32Array(thisPr.execveBuf);

        // may be unnecessary.
        execveWorker.onerror = (err) => {
          console.error("Worker load failed:", err);
          // notify failure to the original worker.
          Atomics.store(execveBufView, 0, 2);
          Atomics.notify(execveBufView, 0, 1);
        }

        // init State.
        execveWorker.postMessage({
          cmd: "startProcess",
          processType: "execved",
          ecvPid: thisPr.ecvPid,
          copyFinBell: thisPr.copyFinBell,
          childMonitor: thisPr.childMonitor,
          parMonitor: thisPr.parMonitor,
          execveBuf: thisPr.execveBuf,
          PTY_AtomicBuffer: PTY_AtomicBuffer,
        });

        // notify success the original process worker.
        Atomics.store(execveBufView, 0, 1);
        Atomics.notify(execveBufView, 0, 1);

      } catch (e) {
        if (typeof FS == "undefined" || !(e.name === "ErrnoError")) throw e;
        return -e.errno;
      }
    }

    function ___syscall_exit(ecvPid, code) {

      try {

        let thisEcvPr = processes.get(ecvPid);

        if (thisEcvPr.childs.size > 0) {
          throw new Error(`The process having childs is not allowed to be exited in the current implementation.`);
        }

        if (thisEcvPr.parent) {
          // has parent
          let monitorView = new Int32Array(thisEcvPr.parMonitor);

          let ringBell = Atomics.load(monitorView, 0);
          if (ringBell != 1) {
            throw new Error(`___syscall_exit must be called when the monitor is locked. ringBell: ${ringBell}`);
          }

          // append the new process to the queue ring.
          let head = Atomics.load(monitorView, 2);
          let tail = Atomics.load(monitorView, 3);

          if (head === (tail + 1) % childProcessMax) {
            throw new Error(`too many processes at ___syscall_exit. head: ${head}, tail: ${tail}.`);
          }

          Atomics.store(monitorView, prLingOffset + tail, ecvPid);
          Atomics.store(monitorView, 3, (tail + 1) % childProcessMax);

          // become no empty. notify to waiting parent process.
          Atomics.store(monitorView, 1, 0);
          Atomics.notify(monitorView, 1, 1);

        } else {
          // init process.
          freeProcessWorker(ecvPid);
        }

      } catch (e) {
        if (typeof FS == "undefined" || !(e.name === "ErrnoError")) throw e;
        return -e.errno;
      }
    }

    function ___syscall_setpgid(tEcvPid, ecvPgid, myEcvPid) {
      try {
        if (tEcvPid == 0) {
          processes.get(myEcvPid).ecvPgid = ecvPgid;
        } else {
          processes.get(tEcvPid).ecvPgid = ecvPgid;
        }
        return 0;
      } catch (e) {
        if (typeof FS == "undefined" || !(e.name === "ErrnoError")) throw e;
        return -1
      }
    }

    function ___syscall_getpgid(tEcvPid, myEcvPid) {
      try {
        return tEcvPid == 0 ? processes.get(myEcvPid).ecvPgid : processes.get(tEcvPid).ecvPgid;
      } catch (e) {
        if (typeof FS == "undefined" || !(e.name === "ErrnoError")) throw e;
        return -1
      }
    }

    function ___syscall_chdir(path) {
      try {
        path = SYSCALLS.getStr(path);
        FS.chdir(path);
        return 0
      } catch (e) {
        if (typeof FS == "undefined" || !(e.name === "ErrnoError")) throw e;
        return -e.errno
      }
    }

    function ___syscall_dup(fd) {
      try {
        var old = SYSCALLS.getStreamFromFD(fd);
        return FS.dupStream(old).fd
      } catch (e) {
        if (typeof FS == "undefined" || !(e.name === "ErrnoError")) throw e;
        return -e.errno
      }
    }

    function ___syscall_dup3(fd, newfd, flags) {
      try {
        var old = SYSCALLS.getStreamFromFD(fd);
        if (old.fd === newfd) return -28;
        if (newfd < 0 || newfd >= FS.MAX_OPEN_FDS) return -8;
        var existingStream = FS.getStream(newfd);
        if (existingStream) FS.close(existingStream.fd);
        return FS.dupStream(old, newfd).fd
      } catch (e) {
        if (typeof FS == "undefined" || !(e.name === "ErrnoError")) throw e;
        return -e.errno
      }
    }

    function ___syscall_faccessat(dirfd, path, amode, flags) {
      try {
        path = SYSCALLS.getStr(path);
        path = SYSCALLS.calculateAt(dirfd, path);
        if (amode & ~7) {
          return -28
        }
        var lookup = FS.lookupPath(path, {
          follow: true
        });
        var node = lookup.node;
        if (!node) {
          return -44
        }
        var perms = "";
        if (amode & 4) perms += "r";
        if (amode & 2) perms += "w";
        if (amode & 1) perms += "x";
        if (perms && FS.nodePermissions(node, perms)) {
          return -2
        }
        return 0
      } catch (e) {
        if (typeof FS == "undefined" || !(e.name === "ErrnoError")) throw e;
        return -e.errno
      }
    }
    var syscallGetVarargI = () => {
      var ret = (growMemViews(gWasmMemory), HEAP32)[+SYSCALLS.varargs >> 2];
      SYSCALLS.varargs += 4;
      return ret
    };
    var syscallGetVarargP = syscallGetVarargI;

    function ___syscall_fcntl64(fd, cmd, varargs) {
      SYSCALLS.varargs = varargs;
      try {
        var stream = SYSCALLS.getStreamFromFD(fd);
        switch (cmd) {
          case 0: {
            var arg = syscallGetVarargI();
            if (arg < 0) {
              return -28
            }
            while (FS.streamMap.get(tEcvPid).get(arg)) {
              arg++
            }
            var newStream;
            newStream = FS.dupStream(stream, arg);
            return newStream.fd
          }
          case 1:
            return stream.fd_flags & FD_CLOEXEC;
          case 2:
            var arg = syscallGetVarargI();
            if (arg != FD_CLOEXEC) {
              console.log(`arg (${arg}) is not FD_CLOEXEC at F_SETFD of fcntl.`);
              abort();
            }
            stream.fd_flags = FD_CLOEXEC;
            return 0;
          case 3:
            return stream.flags;
          case 4: {
            var arg = syscallGetVarargI();
            stream.flags |= arg;
            return 0
          }
          case 12: {
            var arg = syscallGetVarargP();
            var offset = 0;
            (growMemViews(gWasmMemory), HEAP16)[arg + offset >> 1] = 2;
            return 0
          }
          case 13:
          case 14:
            console.log(`fcntl cmd "${cmd}" is not implemented.`);
            abort();
            return 0
        }
        return -28
      } catch (e) {
        if (typeof FS == "undefined" || !(e.name === "ErrnoError")) throw e;
        return -e.errno
      }
    }

    function ___syscall_fstat64(fd, buf) {
      try {
        return SYSCALLS.writeStat(buf, FS.fstat(fd))
      } catch (e) {
        if (typeof FS == "undefined" || !(e.name === "ErrnoError")) throw e;
        return -e.errno
      }
    }
    var INT53_MAX = 9007199254740992;
    var INT53_MIN = -9007199254740992;
    var bigintToI53Checked = num => num < INT53_MIN || num > INT53_MAX ? NaN : Number(num);

    function ___syscall_ftruncate64(fd, length) {
      length = bigintToI53Checked(length);
      try {
        if (isNaN(length)) return -61;
        FS.ftruncate(fd, length);
        return 0
      } catch (e) {
        if (typeof FS == "undefined" || !(e.name === "ErrnoError")) throw e;
        return -e.errno
      }
    }
    var stringToUTF8 = (str, outPtr, maxBytesToWrite) => stringToUTF8Array(str, (growMemViews(gWasmMemory), HEAPU8), outPtr, maxBytesToWrite);

    function ___syscall_getcwd(buf, size) {
      try {
        if (size === 0) return -28;
        var cwd = FS.cwd();
        var cwdLengthInBytes = lengthBytesUTF8(cwd) + 1;
        if (size < cwdLengthInBytes) return -68;
        stringToUTF8(cwd, buf, size);
        return cwdLengthInBytes
      } catch (e) {
        if (typeof FS == "undefined" || !(e.name === "ErrnoError")) throw e;
        return -e.errno
      }
    }

    function ___syscall_getdents64(fd, dirp, count) {
      try {
        var stream = SYSCALLS.getStreamFromFD(fd);
        stream.getdents ||= FS.readdir(stream.path);
        var struct_size = 280;
        var pos = 0;
        var off = FS.llseek(stream, 0, 1);
        var startIdx = Math.floor(off / struct_size);
        var endIdx = Math.min(stream.getdents.length, startIdx + Math.floor(count / struct_size));
        for (var idx = startIdx; idx < endIdx; idx++) {
          var id;
          var type;
          var name = stream.getdents[idx];
          if (name === ".") {
            id = stream.node.id;
            type = 4
          } else if (name === "..") {
            var lookup = FS.lookupPath(stream.path, {
              parent: true
            });
            id = lookup.node.id;
            type = 4
          } else {
            var child;
            try {
              child = FS.lookupNode(stream.node, name)
            } catch (e) {
              if (e?.errno === 28) {
                continue
              }
              throw e
            }
            id = child.id;
            type = FS.isChrdev(child.mode) ? 2 : FS.isDir(child.mode) ? 4 : FS.isLink(child.mode) ? 10 : 8
          }
          (growMemViews(gWasmMemory), HEAP64)[dirp + pos >> 3] = BigInt(id);
          (growMemViews(gWasmMemory), HEAP64)[dirp + pos + 8 >> 3] = BigInt((idx + 1) * struct_size);
          (growMemViews(gWasmMemory), HEAP16)[dirp + pos + 16 >> 1] = 280;
          (growMemViews(gWasmMemory), HEAP8)[dirp + pos + 18] = type;
          stringToUTF8(name, dirp + pos + 19, 256);
          pos += struct_size
        }
        FS.llseek(stream, idx * struct_size, 0);
        return pos
      } catch (e) {
        if (typeof FS == "undefined" || !(e.name === "ErrnoError")) throw e;
        return -e.errno
      }
    }

    function ___syscall_ioctl(fd, op, varargs) {
      SYSCALLS.varargs = varargs;
      try {
        var stream = SYSCALLS.getStreamFromFD(fd);
        switch (op) {
          case 21509: {
            if (!stream.tty) return -59;
            return 0
          }
          case 21505: { // TCGETS
            if (!stream.tty) return -59;
            if (stream.tty.ops.ioctl_tcgets) {
              var termios = stream.tty.ops.ioctl_tcgets(stream);
              var argp = syscallGetVarargP();
              (growMemViews(gWasmMemory), HEAP32)[argp >> 2] = termios.c_iflag || 0;
              (growMemViews(gWasmMemory), HEAP32)[argp + 4 >> 2] = termios.c_oflag || 0;
              (growMemViews(gWasmMemory), HEAP32)[argp + 8 >> 2] = termios.c_cflag || 0;
              (growMemViews(gWasmMemory), HEAP32)[argp + 12 >> 2] = termios.c_lflag || 0;
              for (var i = 0; i < 32; i++) {
                (growMemViews(gWasmMemory), HEAP8)[argp + i + 17] = termios.c_cc[i] || 0
              }
              return 0
            }
            return 0
          }
          case 21510:
          case 21511:
          case 21512: {
            if (!stream.tty) return -59;
            return 0
          }
          case 21506: // TCSETS
          case 21507:
          case 21508: {
            if (!stream.tty) return -59;
            if (stream.tty.ops.ioctl_tcsets) {
              var argp = syscallGetVarargP();
              var c_iflag = (growMemViews(gWasmMemory), HEAP32)[argp >> 2];
              var c_oflag = (growMemViews(gWasmMemory), HEAP32)[argp + 4 >> 2];
              var c_cflag = (growMemViews(gWasmMemory), HEAP32)[argp + 8 >> 2];
              var c_lflag = (growMemViews(gWasmMemory), HEAP32)[argp + 12 >> 2];
              var c_cc = [];
              for (var i = 0; i < 32; i++) {
                c_cc.push((growMemViews(gWasmMemory), HEAP8)[argp + i + 17])
              }
              return stream.tty.ops.ioctl_tcsets(stream.tty, op, {
                c_iflag,
                c_oflag,
                c_cflag,
                c_lflag,
                c_cc
              });
            }
            return 0
          }
          case 21519: { // TIOCGPGRP
            if (!stream.tty) return -59;
            var argp = syscallGetVarargP();
            if (stream.tty.fgPgid <= 0) {
              console.error(`foreground process group id (${stream.tty.fgPgid}) may be invalid? (tty: ${stream.tty})`);
            }
            (growMemViews(gWasmMemory), HEAP32)[argp >> 2] = stream.tty.fgPgid;
            return 0
          }
          case 21520: { // TIOCSPGRP
            if (!stream.tty) return -59;
            return -28
          }
          case 21531: {
            var argp = syscallGetVarargP();
            return FS.ioctl(stream, op, argp);
          }
          case 21523: { // TIOCGWINSZ
            if (!stream.tty) return -59;
            if (stream.tty.ops.ioctl_tiocgwinsz) {
              var winsize = stream.tty.ops.ioctl_tiocgwinsz(stream.tty);
              var argp = syscallGetVarargP();
              (growMemViews(gWasmMemory), HEAP16)[argp >> 1] = winsize[0];
              (growMemViews(gWasmMemory), HEAP16)[argp + 2 >> 1] = winsize[1];
            }
            return 0
          }
          case 21524: {
            if (!stream.tty) return -59;
            return 0
          }
          case 21515: {
            if (!stream.tty) return -59;
            return 0
          }
          case 21584: { // FIONCLEX
            stream.fd_flags &= ~FD_CLOEXEC;
            return 0;
          }
          case 21585: { // FIOCLEX
            stream.fd_flags |= FD_CLOEXEC;
            return 0;
          }
          default:
            return -28
        }
      } catch (e) {
        if (typeof FS == "undefined" || !(e.name === "ErrnoError")) throw e;
        return -e.errno
      }
    }

    // missing coressponding system call number.
    function ___syscall_lstat64(path, buf) {
      try {
        path = SYSCALLS.getStr(path);
        return SYSCALLS.writeStat(buf, FS.lstat(path))
      } catch (e) {
        if (typeof FS == "undefined" || !(e.name === "ErrnoError")) throw e;
        return -e.errno
      }
    }

    function ___syscall_mkdirat(dirfd, path, mode) {
      try {
        path = SYSCALLS.getStr(path);
        path = SYSCALLS.calculateAt(dirfd, path);
        FS.mkdir(path, mode, 0);
        return 0
      } catch (e) {
        if (typeof FS == "undefined" || !(e.name === "ErrnoError")) throw e;
        return -e.errno
      }
    }

    function ___syscall_newfstatat(dirfd, path, buf, flags) {
      try {
        path = SYSCALLS.getStr(path);
        var nofollow = flags & 256;
        var allowEmpty = flags & 4096;
        flags = flags & ~6400;
        path = SYSCALLS.calculateAt(dirfd, path, allowEmpty);
        return SYSCALLS.writeStat(buf, nofollow ? FS.lstat(path) : FS.stat(path))
      } catch (e) {
        if (typeof FS == "undefined" || !(e.name === "ErrnoError")) throw e;
        return -e.errno
      }
    }

    function ___syscall_openat(dirfd, path, flags, varargs) {
      SYSCALLS.varargs = varargs;
      try {
        path = SYSCALLS.getStr(path);
        path = SYSCALLS.calculateAt(dirfd, path);
        var mode = varargs ? syscallGetVarargI() : 0;
        return FS.open(path, flags, mode).fd
      } catch (e) {
        if (typeof FS == "undefined" || !(e.name === "ErrnoError")) throw e;
        return -e.errno
      }
    }

    function ___syscall_poll_scan(fds, nfds, tmSec, tmNsec) {

      growMemViews(gWasmMemory);

      let timeoutSec = 0;
      if (tmSec == -1) {
        timeoutSec = -1;
      } else {
        timeoutSec = tmSec + tmNsec * 1e-9;
      }

      // Scan all FDs for readiness, tolerating PTY "wait again" exceptions.
      let nonzero = 0;
      for (var i = 0; i < nfds; i++) {
        var pollfd = fds + 8 * i;
        var fd = HEAP32[pollfd >> 2];
        var events = HEAP16[pollfd + 4 >> 1];
        var mask = 32;
        var stream = FS.getStream(fd);
        if (stream) {
          if (stream.stream_ops.poll) {
            try {
              mask = stream.stream_ops.poll(stream, events, timeoutSec);
            } catch (e) {
              // PTY throws ErrnoError(1006) when not readable and timeout is set.
              if (e.name === "ErrnoError") {
                mask = 0;
              } else {
                throw e;
              }
            }
          }
        }
        mask &= events | POLLERR | POLLHUP;
        if (mask) nonzero++;
        HEAP16[pollfd + 6 >> 1] = mask;
      }

      // If no FDs are ready, wait for PTY data or timeout.
      if (nonzero === 0 && timeoutSec !== 0) {
        return new Promise(resolve => {
          var timeoutId;
          var handler = PTY.onReadable(() => {
            handler.dispose();
            clearTimeout(timeoutId);
            resolve(0);
          });
          if (timeoutSec > 0) {
            timeoutId = setTimeout(() => {
              handler.dispose();
              resolve(0);
            }, Math.min(timeoutSec * 1000, 30000));
          }
        });
      }

      return nonzero;
    }

    function ___syscall_pselect6_scan(nfds, readfdsP, writefdsP, exceptfdsP, tmSec, tmNsec, sigmaskP) {
      try {

        growMemViews(gWasmMemory);

        let timeout;
        if (tmSec == -1) {
          timeout = -1;
        } else {
          timeout = tmSec + tmNsec * 1e-9;
        }

        function checkFDs(fdsP, events) {

          let tFD = 0;

          for (let i = 0; i < __KERNEL_FD_SETMAXID * 2; i++) { // scan 32 bits at a time.
            for (let j = 0; j < 32; j++) {
              if ((HEAP32[(fdsP >> 2) + i] & (1 << j)) !== 0) {
                let stream = FS.getStream(tFD);
                let mask;
                if (stream) {
                  if (stream.stream_ops.poll) {
                    mask = stream.stream_ops.poll(stream, events, timeout);
                  }
                } else {
                  throw "FS not having stream may be invaild?";
                }
                let fdSetId = tFD / 32;
                let bitId = tFD % 32;
                if (mask & events) {
                  // the bit is set
                  HEAP32[(fdsP >> 2) + fdSetId] |= (1 << bitId);
                  nonzero++;
                } else {
                  // the bit is not set
                  HEAP32[(fdsP >> 2) + fdSetId] &= ~(1 << bitId);
                }
              }
              tFD++;
              if (tFD == nfds) {
                return nonzero;
              }
            }
          }

          return nonzero;
        }

        let nonzero = 0;
        nonzero += checkFDs(readfdsP, POLLIN);
        nonzero += checkFDs(writefdsP, POLLOUT);
        // nonzero += checkFDs(exceptfdsP, null); // rarely not used

        return nonzero;
      } catch (e) {
        if (typeof FS == "undefined" || !(e.name === "ErrnoError")) throw e;
        return -e.errno
      }
    }

    var PTY_ReadableAtomicCheckImpl = callback => {
      if (PTY_pollTimeout === 0) {
        return callback(PTY.readable ? 0 : 2)
      }
      let handlerReadable, handlerSignal, timeoutId;
      new Promise(resolve => {
        handlerReadable = PTY.onReadable(() => resolve(0));
        handlerSignal = PTY.onSignal(() => resolve(1));
        if (PTY_pollTimeout >= 0) {
          timeoutId = setTimeout(resolve, PTY_pollTimeout, 2)
        }
      }).then(type => {
        handlerReadable.dispose();
        handlerSignal.dispose();
        clearTimeout(timeoutId);
        callback(type)
      })
    };
    var PTY_ReadableAtomicCheck = function (atomicBuffer) {
      PTY_ReadableAtomicCheckImpl(type => {
        let PTY_AtomicView = new Int32Array(atomicBuffer);
        Atomics.store(PTY_AtomicView, 0, type);
        Atomics.notify(PTY_AtomicView, 0);
      })
    };

    function ___ecv_get_dev_type(fd) {
      try {
        let stream = FS.getStream(fd);
        return stream.node.mode & S_IFMT;
      } catch (e) {
        if (typeof FS == "undefined" || !(e.name === "ErrnoError")) throw e;
        return -e.errno;
      }
    }

    function ___syscall_readlinkat(dirfd, path, buf, bufsize) {
      try {
        path = SYSCALLS.getStr(path);
        path = SYSCALLS.calculateAt(dirfd, path);
        if (bufsize <= 0) return -28;
        var ret = FS.readlink(path);
        var len = Math.min(bufsize, lengthBytesUTF8(ret));
        var endChar = (growMemViews(gWasmMemory), HEAP8)[buf + len];
        stringToUTF8(ret, buf, bufsize + 1);
        (growMemViews(gWasmMemory), HEAP8)[buf + len] = endChar;
        return len
      } catch (e) {
        if (typeof FS == "undefined" || !(e.name === "ErrnoError")) throw e;
        return -e.errno
      }
    }

    function ___syscall_stat64(path, buf) {
      try {
        path = SYSCALLS.getStr(path);
        return SYSCALLS.writeStat(buf, FS.stat(path))
      } catch (e) {
        if (typeof FS == "undefined" || !(e.name === "ErrnoError")) throw e;
        return -e.errno
      }
    }

    function ___syscall_statfs64(path, size, buf) {
      try {
        SYSCALLS.writeStatFs(buf, FS.statfs(SYSCALLS.getStr(path)));
        return 0
      } catch (e) {
        if (typeof FS == "undefined" || !(e.name === "ErrnoError")) throw e;
        return -e.errno
      }
    }

    function ___syscall_truncate64(path, length) {
      length = bigintToI53Checked(length);
      try {
        if (isNaN(length)) return -61;
        path = SYSCALLS.getStr(path);
        FS.truncate(path, length);
        return 0
      } catch (e) {
        if (typeof FS == "undefined" || !(e.name === "ErrnoError")) throw e;
        return -e.errno
      }
    }

    function ___syscall_unlinkat(dirfd, path, flags) {
      try {
        path = SYSCALLS.getStr(path);
        path = SYSCALLS.calculateAt(dirfd, path);
        if (!flags) {
          FS.unlink(path)
        } else if (flags === 512) {
          FS.rmdir(path)
        } else {
          return -28
        }
        return 0
      } catch (e) {
        if (typeof FS == "undefined" || !(e.name === "ErrnoError")) throw e;
        return -e.errno
      }
    }
    var readI53FromI64 = ptr => (growMemViews(gWasmMemory), HEAPU32)[ptr >> 2] + (growMemViews(gWasmMemory), HEAP32)[ptr + 4 >> 2] * 4294967296;

    function ___syscall_utimensat(dirfd, path, times, flags) {
      try {
        path = SYSCALLS.getStr(path);
        path = SYSCALLS.calculateAt(dirfd, path, true);
        var now = Date.now(),
          atime, mtime;
        if (!times) {
          atime = now;
          mtime = now
        } else {
          var seconds = readI53FromI64(times);
          var nanoseconds = (growMemViews(gWasmMemory), HEAP32)[times + 8 >> 2];
          if (nanoseconds == 1073741823) {
            atime = now
          } else if (nanoseconds == 1073741822) {
            atime = null
          } else {
            atime = seconds * 1e3 + nanoseconds / (1e3 * 1e3)
          }
          times += 16;
          seconds = readI53FromI64(times);
          nanoseconds = (growMemViews(gWasmMemory), HEAP32)[times + 8 >> 2];
          if (nanoseconds == 1073741823) {
            mtime = now
          } else if (nanoseconds == 1073741822) {
            mtime = null
          } else {
            mtime = seconds * 1e3 + nanoseconds / (1e3 * 1e3)
          }
        }
        if ((mtime ?? atime) !== null) {
          FS.utime(path, atime, mtime)
        }
        return 0
      } catch (e) {
        if (typeof FS == "undefined" || !(e.name === "ErrnoError")) throw e;
        return -e.errno
      }
    }
    function ___syscall_chmod(path, mode) {
      try {
        path = SYSCALLS.getStr(path);
        FS.chmod(path, mode);
        return 0
      } catch (e) {
        if (typeof FS == "undefined" || !(e.name === "ErrnoError")) throw e;
        return -e.errno
      }
    }

    function ___syscall_fchmod(fd, mode) {
      try {
        FS.fchmod(fd, mode);
        return 0
      } catch (e) {
        if (typeof FS == "undefined" || !(e.name === "ErrnoError")) throw e;
        return -e.errno
      }
    }

    function ___syscall_fchmodat(dirfd, path, mode, flags) {
      try {
        var nofollow = flags & 256;
        path = SYSCALLS.getStr(path);
        path = SYSCALLS.calculateAt(dirfd, path);
        FS.chmod(path, mode, nofollow);
        return 0
      } catch (e) {
        if (typeof FS == "undefined" || !(e.name === "ErrnoError")) throw e;
        return -e.errno
      }
    }

    function ___syscall_fchownat(dirfd, path, owner, group, flags) {
      try {
        path = SYSCALLS.getStr(path);
        var nofollow = flags & 256;
        flags = flags & ~256;
        path = SYSCALLS.calculateAt(dirfd, path);
        (nofollow ? FS.lchown : FS.chown)(path, owner, group);
        return 0
      } catch (e) {
        if (typeof FS == "undefined" || !(e.name === "ErrnoError")) throw e;
        return -e.errno
      }
    }

    function ___syscall_fdatasync(fd) {
      try {
        var stream = SYSCALLS.getStreamFromFD(fd);
        return 0
      } catch (e) {
        if (typeof FS == "undefined" || !(e.name === "ErrnoError")) throw e;
        return -e.errno
      }
    }

    function ___syscall_renameat(olddirfd, oldpath, newdirfd, newpath) {
      try {
        oldpath = SYSCALLS.getStr(oldpath);
        newpath = SYSCALLS.getStr(newpath);
        oldpath = SYSCALLS.calculateAt(olddirfd, oldpath);
        newpath = SYSCALLS.calculateAt(newdirfd, newpath);
        FS.rename(oldpath, newpath);
        return 0
      } catch (e) {
        if (typeof FS == "undefined" || !(e.name === "ErrnoError")) throw e;
        return -e.errno
      }
    }

    function ___syscall_symlinkat(target, dirfd, linkpath) {
      try {
        target = SYSCALLS.getStr(target);
        linkpath = SYSCALLS.getStr(linkpath);
        linkpath = SYSCALLS.calculateAt(dirfd, linkpath);
        FS.symlink(target, linkpath);
        return 0
      } catch (e) {
        if (typeof FS == "undefined" || !(e.name === "ErrnoError")) throw e;
        return -e.errno
      }
    }

    function _fd_fdstat_get(fd, pbuf) {
      try {
        var rightsBase = 0;
        var rightsInheriting = 0;
        var flags = 0;
        var stream = SYSCALLS.getStreamFromFD(fd);
        var type = stream.tty ? 2 : FS.isDir(stream.mode) ? 3 : FS.isLink(stream.mode) ? 7 : 4;
        (growMemViews(gWasmMemory), HEAP8)[pbuf] = type;
        (growMemViews(gWasmMemory), HEAP16)[pbuf + 2 >> 1] = flags;
        (growMemViews(gWasmMemory), HEAP64)[pbuf + 8 >> 3] = BigInt(rightsBase);
        (growMemViews(gWasmMemory), HEAP64)[pbuf + 16 >> 3] = BigInt(rightsInheriting);
        return 0
      } catch (e) {
        if (typeof FS == "undefined" || !(e.name === "ErrnoError")) throw e;
        return e.errno
      }
    }

    var runtimeKeepaliveCounter = 0;
    var ENV = {};
    var getExecutableName = () => initProcessJsPath;
    var getEnvStrings = () => {
      if (!getEnvStrings.strings) {
        var lang = (typeof navigator == "object" && navigator.languages && navigator.languages[0] || "C").replace("-", "_") + ".UTF-8";
        var env = {
          USER: "web_user",
          LOGNAME: "web_user",
          PATH: "/",
          PWD: "/",
          HOME: "/home/web_user",
          LANG: lang,
          _: getExecutableName()
        };
        for (var x in ENV) {
          if (ENV[x] === undefined) delete env[x];
          else env[x] = ENV[x]
        }
        var strings = [];
        for (var x in env) {
          strings.push(`${x}=${env[x]}`)
        }
        getEnvStrings.strings = strings
      }
      return getEnvStrings.strings
    };

    var keepRuntimeAlive = () => noExitRuntime || runtimeKeepaliveCounter > 0;

    function _proc_exit(code) {
      EXITSTATUS = code;
      if (!keepRuntimeAlive()) {
        Module["onExit"]?.(code);
        ABORT = true
      }
      quit_(code, new ExitStatus(code))
    };
    var exitJS = (status, implicit) => {
      EXITSTATUS = status;
      _proc_exit(status)
    };
    var _exit = exitJS;

    function _fd_close(fd) {
      try {
        FS.close(fd);
        return 0
      } catch (e) {
        if (typeof FS == "undefined" || !(e.name === "ErrnoError")) throw e;
        console.log(e.errno);
        return e.errno
      }
    }
    var doReadv = (stream, iov, iovcnt, offset) => {
      var ret = 0;
      for (var i = 0; i < iovcnt; i++) {
        var ptr = (growMemViews(gWasmMemory), HEAPU32)[iov >> 2];
        var len = (growMemViews(gWasmMemory), HEAPU32)[iov + 4 >> 2];
        iov += 8;
        var curr = FS.read(stream, (growMemViews(gWasmMemory), HEAP8), ptr, len, offset);
        if (curr < 0) return -1;
        ret += curr;
        if (curr < len) break;
        if (typeof offset != "undefined") {
          offset += curr
        }
      }
      return ret
    };

    function ___syscall_pipe2(pipefd, flags) {
      try {
        let path = SYSCALLS.getPipe2NewPath();
        let streamRead = FS.open(path, (flags & ~0b11) | O_CREAT | O_RDONLY, S_IFIFO | 0o600);
        let streamWrite = FS.open(path, (flags & ~0b11) | O_CREAT | O_WRONLY, S_IFIFO | 0o600);
        (growMemViews(gWasmMemory), HEAPU32)[pipefd >> 2] = streamRead.fd;
        (growMemViews(gWasmMemory), HEAPU32)[pipefd + 4 >> 2] = streamWrite.fd;
        SYSCALLS.KERNEL_FIFOS.set(streamRead.node.id, {
          head: 0,
          tail: 0,
        });
        return 0;
      } catch (e) {
        if (typeof FS == "undefined" || !(e.name === "ErrnoError")) throw e;
        return -e.errno;
      }
    }

    function ___syscall_sendfile(out_fd, in_fd, offsetP, count) {
      try {
        let outStream = SYSCALLS.getStreamFromFD(out_fd);
        let inStream = SYSCALLS.getStreamFromFD(in_fd);
        let tmpBuf = new Uint8Array(count);
        // use `read` and `write` instead of directly transportation.
        let readLen;
        if (offsetP) {
          let position = (growMemViews(gWasmMemory), HEAPU32)[offsetP >> 2];
          readLen = FS.read(inStream, tmpBuf, 0, count, position);
          (growMemViews(gWasmMemory), HEAPU32)[offsetP >> 2] = position + readLen;
        } else {
          readLen = FS.read(inStream, tmpBuf, 0, count);
          (growMemViews(gWasmMemory), HEAPU32)[offsetP >> 2] = inStream.position;
        }
        return FS.write(outStream, tmpBuf, 0, readLen, undefined, true);
      } catch (e) {
        if (typeof FS == "undefined" || !(e.name === "ErrnoError")) throw e;
        return -e.errno
      }
    }

    function _fd_read(fd, iov, iovcnt, pnum) {
      try {
        var stream = SYSCALLS.getStreamFromFD(fd);
        var num = doReadv(stream, iov, iovcnt);
        (growMemViews(gWasmMemory), HEAPU32)[pnum >> 2] = num;
        return 0
      } catch (e) {
        if (typeof FS == "undefined" || !(e.name === "ErrnoError")) throw e;
        return e.errno
      }
    }

    function _fd_fifo_read(fd, bufP, len, pnum, bszP) {
      try {
        let stream = SYSCALLS.getStreamFromFD(fd);
        let tFIFO = SYSCALLS.KERNEL_FIFOS.get(stream.node.id);
        if (!tFIFO) {
          throw FS.ErrnoError(106);
        }
        let num = FS.read(stream, (growMemViews(gWasmMemory), HEAP8), bufP, len, tFIFO.head);
        // update ring buffer size.
        if (tFIFO.head + num <= tFIFO.tail) {
          tFIFO.head += num;
        } else {
          throw new Error(`tFIFO head succeeds the tail at calling _fd_fifo_read. node_name: ${stream.node.name}, head: ${tFIFO.head}, tail: ${tFIFO.tail}`)
        }
        // save bsz
        (growMemViews(gWasmMemory), HEAP32)[bszP >> 2] = (tFIFO.tail - tFIFO.head);
        (growMemViews(gWasmMemory), HEAPU32)[pnum >> 2] = num;
        return 0;
      } catch (e) {
        if (typeof FS == "undefined" || !(e.name === "ErrnoError")) throw e;
        return e.errno
      }
    }

    function _fd_seek(fd, offset, whence, newOffset) {
      offset = bigintToI53Checked(offset);
      try {
        if (isNaN(offset)) return 61;
        var stream = SYSCALLS.getStreamFromFD(fd);
        FS.llseek(stream, offset, whence);
        (growMemViews(gWasmMemory), HEAP64)[newOffset >> 3] = BigInt(stream.position);
        if (stream.getdents && offset === 0 && whence === 0) stream.getdents = null;
        return 0
      } catch (e) {
        if (typeof FS == "undefined" || !(e.name === "ErrnoError")) throw e;
        return e.errno
      }
    }

    function _fd_sync(fd) {
      try {
        var stream = SYSCALLS.getStreamFromFD(fd);
        if (stream.stream_ops?.fsync) {
          return stream.stream_ops.fsync(stream)
        }
        return 0
      } catch (e) {
        if (typeof FS == "undefined" || !(e.name === "ErrnoError")) throw e;
        return e.errno
      }
    }
    function _fd_pread(fd, iov, iovcnt, offset, pnum) {
      offset = bigintToI53Checked(offset);
      try {
        if (isNaN(offset)) return 61;
        var stream = SYSCALLS.getStreamFromFD(fd);
        var num = doReadv(stream, iov, iovcnt, offset);
        (growMemViews(gWasmMemory), HEAPU32)[pnum >> 2] = num;
        return 0
      } catch (e) {
        if (typeof FS == "undefined" || !(e.name === "ErrnoError")) throw e;
        return e.errno
      }
    }
    var doWritev = (stream, iov, iovcnt, offset) => {
      var ret = 0;
      for (var i = 0; i < iovcnt; i++) {
        var ptr = (growMemViews(gWasmMemory), HEAPU32)[iov >> 2];
        var len = (growMemViews(gWasmMemory), HEAPU32)[iov + 4 >> 2];
        iov += 8;
        var curr = FS.write(stream, (growMemViews(gWasmMemory), HEAP8), ptr, len, offset);
        if (curr < 0) return -1;
        ret += curr;
        if (curr < len) {
          break
        }
        if (typeof offset != "undefined") {
          offset += curr
        }
      }
      return ret
    };
    function _fd_pwrite(fd, iov, iovcnt, offset, pnum) {
      offset = bigintToI53Checked(offset);
      try {
        if (isNaN(offset)) return 61;
        var stream = SYSCALLS.getStreamFromFD(fd);
        var num = doWritev(stream, iov, iovcnt, offset);
        (growMemViews(gWasmMemory), HEAPU32)[pnum >> 2] = num;
        return 0
      } catch (e) {
        if (typeof FS == "undefined" || !(e.name === "ErrnoError")) throw e;
        return e.errno
      }
    }

    function _fd_write(fd, iov, iovcnt, pnum) {
      try {
        var stream = SYSCALLS.getStreamFromFD(fd);
        var num = doWritev(stream, iov, iovcnt);
        (growMemViews(gWasmMemory), HEAPU32)[pnum >> 2] = num;
        return 0
      } catch (e) {
        if (typeof FS == "undefined" || !(e.name === "ErrnoError")) throw e;
        return e.errno
      }
    }

    function _fd_fifo_write(fd, bufP, len, bszP, pnum) {
      try {
        let stream = SYSCALLS.getStreamFromFD(fd);
        let tFIFO = SYSCALLS.KERNEL_FIFOS.get(stream.node.id);
        if (!tFIFO) {
          throw FS.ErrnoError(106);
        }
        let num = FS.write(stream, (growMemViews(gWasmMemory), HEAP8), bufP, len); // offset is skipeed same as to `_fd_write`.
        // update ring buffer position.
        if (tFIFO.tail + len <= PIPE_MAX_SZ) {
          tFIFO.tail += len;
        } else {
          throw new Error(`tFIFO tail succeeds 'PIPE_MAX_SZ' at calling _fd_fifo_write. node_name: ${stream.node.name}, head: ${tFIFO.head}, tail: ${tFIFO.tail}`);
        }
        // save bsz
        (growMemViews(gWasmMemory), HEAP32)[bszP >> 2] = (tFIFO.tail - tFIFO.head);
        (growMemViews(gWasmMemory), HEAPU32)[pnum >> 2] = num;
        return 0;
      } catch (e) {
        if (typeof FS == "undefined" || !(e.name === "ErrnoError")) throw e;
        return e.errno
      }
    }

    function _random_get(buffer, size) {
      try {
        randomFill((growMemViews(gWasmMemory), HEAPU8).subarray(buffer, buffer + size));
        return 0
      } catch (e) {
        if (typeof FS == "undefined" || !(e.name === "ErrnoError")) throw e;
        return e.errno
      }
    }

    FS.createPreloadedFile = FS_createPreloadedFile;
    FS.staticInit();
    MEMFS.doesNotExistError = new FS.ErrnoError(44);
    MEMFS.doesNotExistError.stack = "<generic error, no stack>";
    {
      if (Module["noExitRuntime"]) noExitRuntime = Module["noExitRuntime"];
      if (Module["preloadPlugins"]) preloadPlugins = Module["preloadPlugins"];
      if (Module["print"]) out = Module["print"];
      if (Module["printErr"]) err = Module["printErr"];
      if (Module["arguments"]) arguments_ = Module["arguments"];
    }

    function run(args = arguments_) {
      if (runDependencies > 0) {
        dependenciesFulfilled = run;
        return
      }
      preRun();
      if (runDependencies > 0) {
        dependenciesFulfilled = run;
        return
      }

      async function doRun() {
        await initRuntime();

        // Load Python libraries after FS is initialized
        if (Module["loadPackage"] && Module["pythonLibraryMetadata"] && !Module["pythonLibrariesLoaded"]) {
          Module["pythonLibrariesLoaded"] = true;
          console.log("Loading Python libraries after initRuntime...");
          Module["loadPackage"](Module["pythonLibraryMetadata"]);
          if (runDependencies > 0) {
            await new Promise(resolve => { dependenciesFulfilled = resolve; });
          }
        }

        preMain();
        readyPromiseResolve(Module);
        postRun()
      }
      if (Module["setStatus"]) {
        Module["setStatus"]("Running...");
        setTimeout(() => {
          setTimeout(() => Module["setStatus"](""), 1);
          doRun()
        }, 1)
      } else {
        doRun()
      }
    }

    function preInit() {
      if (Module["preInit"]) {
        if (typeof Module["preInit"] == "function") Module["preInit"] = [Module["preInit"]];
        while (Module["preInit"].length > 0) {
          Module["preInit"].shift()()
        }
      }
    }

    preInit();
    run();

    moduleRtn = readyPromise;
    return moduleRtn;
  });
})();
export default Module;