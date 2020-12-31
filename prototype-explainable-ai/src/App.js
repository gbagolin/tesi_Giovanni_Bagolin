import './App.css';
import React, { useState } from 'react';
import Navbar from './Navbar'
import Title from './Title'
import Button from './Button'
import Modal from './Modal'

function App() {
  return (
    <>
      <Navbar />
      <div className="container-fluid">
        <Title />
        <Button />
        <Modal />
      </div>
    </>
  )
}

export default App;
