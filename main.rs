//Authors: Michael Roytman and Anna Yatskar
//Class: CoSi 146: Complex Systems Design
//Project: Programming Assignment 3 - Part B: Zhtta Web Server
//Professor: Professor Shrira
//Date: May 1, 2015

//
// zhtta.rs
//
// Starting code for PA3
// Revised to run on Rust 1.0.0 nightly - built 02-21
//
// Note that this code has serious security risks!  You should not run it 
// on any system with access to sensitive files.
// 
// Brandeis University - cs146a Spring 2015
// Dimokritos Stamatakis and Brionne Godby
// Version 1.0

// To see debug! outputs set the RUST_LOG environment variable, e.g.: export RUST_LOG="zhtta=debug"

#![allow(deprecated)]
#![allow(dead_code)]
#![allow(unused_variables)]
#![allow(unused_imports)]
#![allow(unused_parens)]
#![allow(unused_assignments)]

#![feature(process)]
#![feature(rustc_private)]
#![feature(libc)]
#![feature(io)]
#![feature(old_io)]
#![feature(old_path)]
#![feature(os)]
#![feature(core)]
#![feature(collections)]
#![feature(std_misc)]
#![allow(non_camel_case_types)]
#![allow(unused_must_use)]
#![allow(deprecated)]
#[macro_use]
extern crate log;
extern crate libc;

use std::io::*;
use std::{os, str};
use std::old_path::posix::Path;
use std::collections::hash_map::HashMap;
use std::borrow::ToOwned;
use std::thread::Thread;
use std::old_io::fs::PathExtensions;
use std::old_io::{Acceptor, Listener, File, BufferedReader, timer};
use std::cell::Cell;
use std::process::Command;
use std::collections::BinaryHeap;
use std::cmp::*;
use std::time::Duration;
use core::num::ToPrimitive;
use std::sync::{Arc, Mutex, Condvar, RwLock};
use std::sync::mpsc::{Sender, Receiver, channel};

extern crate core;

mod gash;

extern crate regex;
extern crate getopts;
use getopts::{optopt, getopts};


//the maximum number of concurrent tasks used to service static HTTP requests
static TASK_AMOUNT: i32 = 10;

//sleep for variable that determines how long to sleep a waiting thread for
static SLEEP_FOR: i64 = 1;

//the file chunk size sent to the output stream at a time as the file is read
const FILE_STREAM_SIZE: usize = 256;

static SERVER_NAME : &'static str = "Zhtta Version 1.0";

static IP : &'static str = "127.0.0.1";
static PORT : usize = 4414;
static WWW_DIR : &'static str = "./www";

static HTTP_OK : &'static str = "HTTP/1.1 200 OK\r\nContent-Type: text/html; charset=UTF-8\r\n\r\n";
static HTTP_BAD : &'static str = "HTTP/1.1 404 Not Found\r\n\r\n";

static COUNTER_STYLE : &'static str = "<doctype !html><html><head><title>Hello, Rust!</title>
             <style>body { background-color: #884414; color: #FFEEAA}
                    h1 { font-size:2cm; text-align: center; color: black; text-shadow: 0 0 4mm red }
                    h2 { font-size:2cm; text-align: center; color: black; text-shadow: 0 0 4mm green }
             </style></head>
             <body>";

struct HTTP_Request  {
    // Use peer_name as the key to access TcpStream in hashmap. 

    // (Due to a bug in extra::arc in Rust 0.9, it is very inconvenient to use TcpStream without the "Freeze" bound.
    //  See issue: https://github.com/mozilla/rust/issues/12139)
    peer_name: String,
    path: Path,
    priority: u64,
    file_size: usize,
}

//implements ordering for HTTP_Request for use in BinaryHeap (smart scheduling) by implementing methods necessary by interface
impl Ord for HTTP_Request {
    fn cmp(&self, other: &HTTP_Request) -> Ordering {
        if other.priority > self.priority {
            return Ordering::Greater
        }
        else if other.priority < self.priority {
            return Ordering::Less
        }
        else {
            return Ordering::Equal
        }
    }
}

impl PartialOrd for HTTP_Request {
    fn partial_cmp(&self, other: &HTTP_Request) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialEq for HTTP_Request {
    fn eq(&self, other: &HTTP_Request) -> bool {
        return self.priority == other.priority
    }
}

impl Eq for HTTP_Request {}

struct WebServer {
    ip: String,
    port: usize,
    www_dir_path: Path,
    file_stream_size: usize,
    task_amount: i32,
    
    //arc wrapped around mutex protecting a cell containing visitor count
    task_count_arc: Arc<Mutex<Cell<i32>>>,

    //arc wrapped around a mutex protecting a BinaryHeap of HTTP_Requests
    request_queue_arc: Arc<Mutex<BinaryHeap<HTTP_Request>>>, 

    stream_map_arc: Arc<Mutex<HashMap<String, std::old_io::net::tcp::TcpStream>>>,
    
    notify_rx: Receiver<()>,
    notify_tx: Sender<()>,
}

impl WebServer {
    fn new(ip: String, port: usize, www_dir: String, task_amount: i32, file_stream_size: usize) -> WebServer {
        let (notify_tx, notify_rx) = channel();
        let www_dir_path = Path::new(www_dir);
        os::change_dir(&www_dir_path);

        WebServer {
            ip:ip,
            port: port,
            www_dir_path: www_dir_path,
            task_amount: task_amount,
            file_stream_size: file_stream_size, 

            task_count_arc: Arc::new(Mutex::new(Cell::new(0))),
            request_queue_arc: Arc::new(Mutex::new(BinaryHeap::new())), 
            stream_map_arc: Arc::new(Mutex::new(HashMap::new())),

            notify_rx: notify_rx,
            notify_tx: notify_tx,
        }
    }
    
    fn run(&mut self) {
        self.listen();
        let task_count_arc = self.task_count_arc.clone();
        self.dequeue_static_file_request(task_count_arc);
    }
    
    fn listen(&mut self) {
    	let addr = String::from_str(format!("{}:{}", self.ip, self.port).as_slice());
        
        let www_dir_path_str = self.www_dir_path.clone();
        let request_queue_arc = self.request_queue_arc.clone();
        let notify_tx = self.notify_tx.clone();
        let stream_map_arc = self.stream_map_arc.clone();

        let visit_count : Arc<Mutex<Cell<i32>>> = Arc::new(Mutex::new(Cell::new(0)));
        
        Thread::spawn(move|| {
        	let listener = std::old_io::TcpListener::bind(addr.as_slice()).unwrap();
            let mut acceptor = listener.listen().unwrap();
            println!("{} listening on {} (serving from: {}).", 
                     SERVER_NAME, addr, www_dir_path_str.as_str().unwrap());
            for stream_raw in acceptor.incoming() {
                let (queue_tx, queue_rx) = channel();
                queue_tx.send(request_queue_arc.clone());
                
                let notify_chan = notify_tx.clone();
                let stream_map_arc = stream_map_arc.clone();
                let vc = visit_count.clone();

                // Spawn a task to handle the connection.
                Thread::spawn(move|| {
                	
                	//increments visitor count for each new request
                    {
                		let visitor_count = vc.lock().unwrap();
                		visitor_count.set(visitor_count.get()+1);
                	}

                    let request_queue_arc = queue_rx.recv().unwrap();
                    let mut stream = match stream_raw {
                        Ok(s) => {s}
				        Err(e) => { panic!("Error getting the listener stream! {}", e) }
				    };
                    let peer_name = WebServer::get_peer_name(&mut stream);
                    debug!("Got connection from {}", peer_name);
                    let mut buf: [u8;500] = [0;500];
                    stream.read(&mut buf);
                    let request_str = match str::from_utf8(&buf){
                        Ok(s) => s,
                        Err(e)=> panic!("Error reading from the listener stream! {}", e),
                    };
                    debug!("Request:\n{}", request_str);
                    let req_group: Vec<&str> = request_str.splitn(3, ' ').collect();
                    if req_group.len() > 2 {
                        let path_str = ".".to_string() + req_group[1];
                        let mut path_obj = os::getcwd().unwrap();
                        path_obj.push(path_str.clone());
                        let ext_str = match path_obj.extension_str() {
                            Some(e) => e,
                            None => "",
                        };
                       
                        debug!("Requested path: [{}]", path_obj.as_str().expect("error"));
                        debug!("Requested path: [{}]", path_str);

                        if path_str.as_slice().eq("./")  {
                            debug!("===== Counter Page request =====");
                            WebServer::respond_with_counter_page(stream, vc.clone());
                            debug!("=====Terminated connection from [{}].=====", peer_name);
                        }  else if !path_obj.exists() || path_obj.is_dir() {
                            debug!("===== Error page request =====");
                            WebServer::respond_with_error_page(stream, &path_obj);
                            debug!("=====Terminated connection from [{}].=====", peer_name);
                        } else if ext_str == "shtml" { // Dynamic web pages.
                            debug!("===== Dynamic Page request =====");
                            WebServer::respond_with_dynamic_page(stream, &path_obj);
                            debug!("=====Terminated connection from [{}].=====", peer_name);
                       } else { 
                            debug!("===== Static Page request =====");
                            WebServer::enqueue_static_file_request(stream, &path_obj, stream_map_arc, request_queue_arc, notify_chan);
                        }
                    }
                });
            }
		});
    }

    fn respond_with_error_page(stream: std::old_io::net::tcp::TcpStream, path: &Path) {
		let mut stream = stream;
		let msg: String= format!("Cannot open: {}", path.as_str().expect("invalid path"));
		stream.write(HTTP_BAD.as_bytes());
		stream.write(msg.as_bytes());
    }

    //Safe visitor counter.
    fn respond_with_counter_page(stream: std::old_io::net::tcp::TcpStream, visitor_count_arc : Arc<Mutex<Cell<i32>>>) {
        let mut stream = stream;
        let response: String = 
            format!("{}{}<h1>Greetings, Krusty!</h1><h2>Visitor count: {}</h2></body></html>\r\n", 
                    HTTP_OK, COUNTER_STYLE, visitor_count_arc.lock().unwrap().get());
        debug!("Responding to counter request");
        stream.write(response.as_bytes());
    }
    
     // TODO: Streaming file.
    // TODO: Application-layer file caching.
    fn respond_with_static_file(stream: std::old_io::net::tcp::TcpStream, path: &Path, file_stream_size: usize, file_size: usize) {
        println!("starting {:?}", path);
        let mut stream = stream;
        let mut file_reader = File::open(path).unwrap();
        stream.write(HTTP_OK.as_bytes());

        let mut remaining_bytes: usize = file_size;

        while remaining_bytes >= file_stream_size {
            let mut buffer: [u8; FILE_STREAM_SIZE] = [0; FILE_STREAM_SIZE];
            let read = file_reader.read(&mut buffer);

            //println!("we read this many bytes: {}", read.unwrap());

            remaining_bytes -= file_stream_size;
            stream.write(&buffer);
        }

        let mut buffer:  [u8; FILE_STREAM_SIZE] = [0; FILE_STREAM_SIZE];
        let read = file_reader.read(&mut buffer);

        //println!("we read this many bytes left over: {}", read.unwrap());

        stream.write(&buffer[0..remaining_bytes]);
    }
    
    // TODO: Server-side gashing.
    fn respond_with_dynamic_page(stream: std::old_io::net::tcp::TcpStream, path: &Path) {
        let file_reader = File::open(&path).unwrap();

        let mut buffered_reader = BufferedReader::new(file_reader);
        let reg = regex::Regex::new("<!--#exec cmd=\"(.+?)\" -->").unwrap();

        stream.clone().write(HTTP_OK.as_bytes());

        let console = gash::Shell::new("");

        for line in buffered_reader.lines() {
    
            let line = line.unwrap();

            let caps = match reg.captures(&line) {
                None => {stream.clone().write(line.as_bytes()); continue;},
                Some(result) => result,
            };

            let command = caps.at(1).unwrap();

            let result = console.run_cmdline_gash(command);

            let new_line = reg.replace_all(&line, result.as_slice());

            stream.clone().write(new_line.as_bytes());
            
        }
    }
    
    // TODO: Smarter Scheduling.
    fn enqueue_static_file_request(stream: std::old_io::net::tcp::TcpStream, path_obj: &Path, stream_map_arc: Arc<Mutex<HashMap<String, std::old_io::net::tcp::TcpStream>>>, req_queue_arc: Arc<Mutex<BinaryHeap<HTTP_Request>>>, notify_chan: Sender<()>) {
    	// Save stream in hashmap for later response.
        let mut stream = stream;
        let peer_name = WebServer::get_peer_name(&mut stream);
    
        let (stream_tx, stream_rx) = channel();
        stream_tx.send(stream);
        let stream = match stream_rx.recv(){
            Ok(s) => s,
            Err(e) => panic!("There was an error while receiving from the stream channel! {}", e),
        };
        let local_stream_map = stream_map_arc.clone();
        {   // make sure we request the lock inside a block with different scope, so that we give it back at the end of that block
            let mut local_stream_map = local_stream_map.lock().unwrap();
            local_stream_map.insert(peer_name.clone(), stream);
        }

        // Enqueue the HTTP request.

        let file_size = path_obj.stat().unwrap().size;

        let file_size_usize = file_size.to_uint().unwrap();

        // TOCHECK: it was ~path_obj.clone(), make sure in which order are ~ and clone() executed
        let req = HTTP_Request { peer_name: peer_name.clone(), path: path_obj.clone(), priority: file_size, file_size: file_size_usize};
        let (req_tx, req_rx) = channel();
        req_tx.send(req);
        debug!("Waiting for queue mutex lock.");
        
        let local_req_queue = req_queue_arc.clone();
        {   // make sure we request the lock inside a block with different scope, so that we give it back at the end of that block
            let mut local_req_queue = local_req_queue.lock().unwrap();
            let req: HTTP_Request = match req_rx.recv(){
                Ok(s) => s,
                Err(e) => panic!("There was an error while receiving from the request channel! {}", e),
            };
            local_req_queue.push(req); //now a binary heap

            debug!("A new request enqueued, now the length of queue is {}.", local_req_queue.len());
            notify_chan.send(()); // Send incoming notification to responder task. 
        }
    }
    
    // TODO: Smarter Scheduling.
    fn dequeue_static_file_request(&mut self, task_count_arc: Arc<Mutex<Cell<i32>>>) {
        let req_queue_get = self.request_queue_arc.clone();
        let stream_map_get = self.stream_map_arc.clone();

        // Receiver<> cannot be sent to another task. So we have to make this task as the main task that can access self.notify_rx.
        let (request_tx, request_rx) = channel();
        loop {
            
            {
                let task_count_int = task_count_arc.lock().unwrap();
                task_count_int.set(task_count_int.get()+1);
            }


            self.notify_rx.recv();    // waiting for new request enqueued.
            {   // make sure we request the lock inside a block with different scope, so that we give it back at the end of that block
                let mut req_queue = req_queue_get.lock().unwrap();
                if req_queue.len() > 0 {
                    let req = req_queue.pop().unwrap(); //PUT MATCH BLOCK FOR DEBUGGING PURPOSES (SAYS DIMOS)
                    debug!("A new request dequeued, now the length of queue is {}.", req_queue.len());
                    request_tx.send(req);
                }
            }

            let request = match request_rx.recv(){
                Ok(s) => s,
                Err(e) => panic!("There was an error while receiving from the request channel! {}", e),
            };
            // Get stream from hashmap.
            let (stream_tx, stream_rx) = channel();
            {   // make sure we request the lock inside a block with different scope, so that we give it back at the end of that block
                let mut stream_map = stream_map_get.lock().unwrap();
                let stream = stream_map.remove(&request.peer_name).expect("no option tcpstream");
                stream_tx.send(stream);
            }
            //Spawning more tasks to respond the dequeued requests concurrently. You may need a semophore to control the concurrency.

            let task_count_arc = task_count_arc.clone();

            //waits thread for one second
            while task_count_arc.lock().unwrap().get() == TASK_AMOUNT {
                //put this task to sleep for 1 second
                timer::sleep(Duration::seconds(SLEEP_FOR));
            }

            Thread::spawn(move|| {

                let stream = match stream_rx.recv(){
                    Ok(s) => s,
                    Err(e) => panic!("There was an error while receiving from the stream channel! {}", e),
                };

                WebServer::respond_with_static_file(stream, &request.path, FILE_STREAM_SIZE, request.file_size);
                // Close stream automatically.
                debug!("=====Terminated connection from [{}].=====", request.peer_name);

                {
                    let task_count_int = task_count_arc.lock().unwrap();
                    task_count_int.set(task_count_int.get()-1);
                }
            });
        }
    }
    
    fn get_peer_name(stream: &mut std::old_io::net::tcp::TcpStream) -> String{
        match stream.peer_name(){
            Ok(s) => {format!("{}:{}", s.ip, s.port)}
            Err(e) => {panic!("Error while getting the stream name! {}", e)}
        }
    }
}

fn get_args() -> (String, usize, String, i32, usize) {
	fn print_usage(program: &str) {
        println!("Usage: {} [options]", program);
        println!("--ip     \tIP address, \"{}\" by default.", IP);
        println!("--port   \tport number, \"{}\" by default.", PORT);
        println!("--www    \tworking directory, \"{}\" by default", WWW_DIR);
        println!("-h --help \tUsage");
    }
    
    /* Begin processing program arguments and initiate the parameters. */
    let args = os::args();
    let program = args[0].clone();
    
    let opts = [
        getopts::optopt("", "ip", "The IP address to bind to", "IP"),
        getopts::optopt("", "port", "The Port to bind to", "PORT"),
        getopts::optopt("", "www", "The www directory", "WWW_DIR"),
        getopts::optopt("", "task_amount", "The maximum number of tasks to service requests", "TASK_AMOUNT"),
        getopts::optopt("", "file_stream_size", "The file chunk size sent to the output stream as the file is read", "STREAM_SIZE"),
        getopts::optflag("h", "help", "Display help"),
    ];

    let matches = match getopts::getopts(args.tail(), &opts) {
        Ok(m) => { m }
        Err(f) => { panic!(f.to_err_msg()) }
    };

    if matches.opt_present("h") || matches.opt_present("help") {
        print_usage(program.as_slice());
        unsafe { libc::exit(1); }
    }
    
    let ip_str = if matches.opt_present("ip") {
                    matches.opt_str("ip").expect("invalid ip address?").to_owned()
                 } else {
                    IP.to_owned()
                 };
    
    let port:usize = if matches.opt_present("port") {
        let input_port = matches.opt_str("port").expect("Invalid port number?").trim().parse::<usize>().ok();
        match input_port {
            Some(port) => port,
            None => panic!("Invalid port number?"),
        }
    } else {
        PORT
    };
    
    let www_dir_str = if matches.opt_present("www") {
                        matches.opt_str("www").expect("invalid www argument?") 
                      } else { WWW_DIR.to_owned() };

    let task_amount: i32 = if matches.opt_present("task_amount") {
        let input_task_amount = matches.opt_str("task_amount").expect("Invalid task_amount number?").trim().parse::<i32>().ok();
        match input_task_amount {
            Some(task_amount) => task_amount,
            None => panic!("Invalid task_amount number?"),
        }
    } else {
            TASK_AMOUNT
    };

    let file_stream_size: usize = if matches.opt_present("file_stream_size") {
        let input_file_stream_size = matches.opt_str("file_stream_size").expect("Invalid file_stream_size number?").trim().parse::<usize>().ok();
        match input_file_stream_size {
            Some(file_stream_size) => file_stream_size,
            None => panic!("Invalid file_stream_size number?"),
        }
    } else {
            FILE_STREAM_SIZE
    };

    (ip_str, port, www_dir_str, task_amount, file_stream_size)    
}

fn main() {
    let (ip_str, port, www_dir_str, task_amount, file_stream_size) = get_args();
    let mut zhtta =  WebServer::new(ip_str, port, www_dir_str, task_amount, file_stream_size);
    zhtta.run();
}
