import * as NodeJSStream from "stream";

interface LogEntry {
  level: string;
  message: string;
  [optionName: string]: any;
}

interface LogMethod {
  (level: string, message: string, callback: LogCallback): Logger;
  (level: string, message: string, meta: any, callback: LogCallback): Logger;
  (level: string, message: string, ...meta: any[]): Logger;
  (entry: LogEntry): Logger;
  (level: string, message: any): Logger;
}

interface LeveledLogMethod {
  (message: string, callback: LogCallback): Logger;
  (message: string, meta: any, callback: LogCallback): Logger;
  (message: string, ...meta: any[]): Logger;
  (message: any): Logger;
  (infoObject: object): Logger;
}

interface WinstonLogger extends NodeJSStream.Transform {
  log: LogMethod;
  clear(): Logger;
  close(): Logger;

  error: LeveledLogMethod;
  warn: LeveledLogMethod;
  help: LeveledLogMethod;
  data: LeveledLogMethod;
  info: LeveledLogMethod;
  debug: LeveledLogMethod;
  prompt: LeveledLogMethod;
  http: LeveledLogMethod;
  verbose: LeveledLogMethod;
  input: LeveledLogMethod;
  silly: LeveledLogMethod;

  emerg: LeveledLogMethod;
  alert: LeveledLogMethod;
  crit: LeveledLogMethod;
  warning: LeveledLogMethod;
  notice: LeveledLogMethod;

  isLevelEnabled(level: string): boolean;
  isErrorEnabled(): boolean;
  isWarnEnabled(): boolean;
  isInfoEnabled(): boolean;
  isVerboseEnabled(): boolean;
  isDebugEnabled(): boolean;
  isSillyEnabled(): boolean;
}
